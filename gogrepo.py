#!/usr/bin/env python
# -*- coding: utf-8 -*-
from __future__ import print_function
from __future__ import division
from __future__ import unicode_literals

__appname__ = "gogrepo.py"
__author__ = "eddie3"
__version__ = "0.3a"
__url__ = "https://github.com/eddie3/gogrepo"

# imports
import argparse
import codecs
import contextlib
import datetime
import getpass
import hashlib
import html5lib
import io
import json
import logging
import numpy
import os
import pprint
import re
import shutil
import shutil
import socket
import sys
import threading
import time
import xml.etree.ElementTree
import zipfile



# python 2 / 3 imports
try:
    # python 2
    from Queue import Queue
    import cookielib as cookiejar
    from httplib import BadStatusLine
    from urlparse import urlparse
    from urllib import urlencode, unquote
    from urllib2 import HTTPError, URLError, HTTPCookieProcessor, build_opener, Request
    from itertools import izip_longest as zip_longest
    from StringIO import StringIO
except ImportError:
    # python 3
    from queue import Queue
    import http.cookiejar as cookiejar
    from http.client import BadStatusLine
    from urllib.parse import urlparse, urlencode, unquote
    from urllib.request import (HTTPCookieProcessor, HTTPError, URLError, build_opener, Request)
    from itertools import zip_longest
    from io import StringIO

# python 2 / 3 renames
try:
    input = raw_input
except NameError:
    pass

# optional imports
try:
    from html2text import html2text
except ImportError:
    def html2text(x):
        return x

# lib mods
# bypass the hardcoded "Netscape HTTP Cookie File" check
cookiejar.MozillaCookieJar.magic_re = r".*"

# configure logging
logFormatter = logging.Formatter("%(asctime)s | %(message)s", datefmt="%H:%M:%S")
consoleHandler = logging.StreamHandler(sys.stdout)
consoleHandler.setFormatter(logFormatter)
rootLogger = logging.getLogger("ws")
rootLogger.setLevel(logging.INFO)
rootLogger.addHandler(consoleHandler)

# logging aliases
info = rootLogger.info
warn = rootLogger.warning
debug = rootLogger.debug
error = rootLogger.error
log_exception = rootLogger.exception

# filepath constants
GAME_STORAGE_DIR = r"."
IMAGE_FILENAME = r"folder.jpg"
COOKIES_FILENAME = r"gog-cookies.dat"
MANIFEST_FILENAME = r"gog-manifest.dat"

# global web utilities
global_cookies = cookiejar.LWPCookieJar(COOKIES_FILENAME)
cookieproc = HTTPCookieProcessor(global_cookies)
opener = build_opener(cookieproc)
treebuilder = html5lib.treebuilders.getTreeBuilder("etree")
parser = html5lib.HTMLParser(tree=treebuilder, namespaceHTMLElements=False)

# GOG URLs
GOG_HOME_URL = r"https://www.gog.com"
GOG_ACCOUNT_URL = r"https://www.gog.com/account"
GOG_LOGIN_URL = r"https://login.gog.com/login_check"

# GOG Constants
GOG_MEDIA_TYPE_ALL = "0"
GOG_MEDIA_TYPE_GAME = "1"
GOG_MEDIA_TYPE_MOVIE = "2"

# HTTP request settings
HTTP_FETCH_DELAY = 0  # in seconds
HTTP_RETRY_DELAY = 3  # in seconds
HTTP_RETRY_COUNT = 5
HTTP_GAME_DOWNLOADER_THREADS = 2
HTTP_PERM_ERRORCODES = (404, 403, 503)
HTTP_DOWNLOAD_SPEED = 5 # MB / s

# Save manifest data for these os and lang combinations
DEFAULT_OS_LIST = ["windows"]
DEFAULT_LANG_LIST = ["English"]

# These file types don't have md5 data from GOG
SKIP_MD5_FILE_EXT = [".txt", ".zip"]

ORPHAN_DIR_NAME = "!orphaned"
ORPHAN_DIR_EXCLUDE_LIST = [ORPHAN_DIR_NAME, "!misc"]

EXCLUDED_IDS = [
    1207664643,     # The Witcher 3 base
    1806891286,     # Bioshock 2 base
    2022341186      # Bioshock base
]

READER = codecs.getreader("utf-8")

GAMES = []
MOVIES = []



class HeaderException(Exception):
    pass


def load_manifest():
    global GAMES
    GAMES = []

    global MOVIES
    MOVIES = []

    if os.path.isfile(MANIFEST_FILENAME):
        with codecs.open(MANIFEST_FILENAME, mode='r', endoding='utf-8') as infile:
            manifest = json.load(infile)
            GAMES = manifest.get("games", [])
            MOVIES = manifest.get("movies", [])


def save_manifest():
    with codecs.open(MANIFEST_FILENAME, mode='w', encoding='utf-8') as outfile:
        collection = {'games': sorted(GAMES, key=lambda game: game["title"]), 'movies': sorted(MOVIES, key=lambda movie: movie["title"])}
        json.dump(collection, outfile, ensure_ascii=False, indent=3)


def request(url, args=None, byte_range=None, retries=HTTP_RETRY_COUNT, delay=HTTP_FETCH_DELAY, check_headers=None):
    _retry = False
    time.sleep(delay)

    try:
        if args is None:
            enc_args = None
        else:
            enc_args = urlencode(args)
            enc_args = enc_args.encode("ascii")  # needed for Python 3

        req = Request(url, data=enc_args)

        if byte_range is not None:
            req.add_header("Range", "bytes=%d-%d" % byte_range)

        page = opener.open(req)

        if check_headers is not None:
            (header, pattern) = check_headers
            if header not in page.headers:
                raise HeaderException()
            else:
                if (pattern is not None) and not (re.compile(pattern).search(page.headers[header].split()[-1])):
                    warn(pattern)
                    warn(page.headers[header].split()[-1])
                    raise HeaderException()

    except (HTTPError, URLError, socket.error, BadStatusLine, HeaderException) as e:
        if isinstance(e, HTTPError):
            if e.code in HTTP_PERM_ERRORCODES:  # do not retry these HTTP codes
                warn("request failed: %s.  will not retry.", e)
                raise

        if retries > 0:
            _retry = True
        else:
            raise

        if _retry:
            warn("request failed: %s (%d retries left) -- will retry in %ds..." % (e, retries, HTTP_RETRY_DELAY))
            return request(url=url, args=args, byte_range=byte_range, retries=retries - 1, delay=HTTP_RETRY_DELAY, check_headers=check_headers)

    return contextlib.closing(page)


def pretty_size(n):
    for unit in ["B", "KB", "MB", "GB"]:
        if n < 1024 or unit == "GB":
            break
        n = n / 1024  # start at KB

    if unit == "B":
        return "{}  {}".format(n, unit)
    else:
        return "{:.2f} {}".format(n, unit)


def item_checkdb(value, collection, field):
    for i in range(len(collection)):
        if value == collection[i][field]:
            return i
    return None

def cleanString(string):
    return string.replace("™", "").replace("®", "").replace("’", "'").replace("\t", "").replace("<br>", " ").strip()



""" COMMANDS """
def cmd_login():
    def fetchAuthURL(login_data):
        info("attempting gog login as '{}' ...".format(login_data["user"]))
        with request(GOG_HOME_URL, delay=0) as page:
            etree = html5lib.parse(page, namespaceHTMLElements=False)
            for elm in etree.findall(".//script"):
                if elm.text is not None and "GalaxyAccounts" in elm.text:
                    login_data["auth_url"] = elm.text.split("'")[3]
                    break

    def fetchLoginToken(login_data):
        with request(login_data["auth_url"], delay=0) as page:
            etree = html5lib.parse(page, namespaceHTMLElements=False)
            if len(etree.findall('.//div[@class="g-recaptcha form__recaptcha"]')) > 0:
                error("cannot continue, GOG is asking for a reCAPTCHA :(  try again in a few minutes.")
                sys.exit(1)

            for elm in etree.findall(".//input"):
                if elm.attrib["id"] == "login__token":
                    login_data["login_token"] = elm.attrib["value"]
                    break

    def tryBasicLogin(login_data):
        with request(GOG_LOGIN_URL, delay=0, args={"login[username]": login_data["user"], "login[password]": login_data["passwd"], "login[login]": "", "login[_token]": login_data["login_token"]}) as page:
            etree = html5lib.parse(page, namespaceHTMLElements=False)
            if "two_step" in page.geturl():
                login_data["two_step_url"] = page.geturl()
                for elm in etree.findall(".//input"):
                    if elm.attrib["id"] == "second_step_authentication__token":
                        login_data["two_step_token"] = elm.attrib["value"]
                        break

            elif "on_login_success" in page.geturl():
                login_data["login_success"] = True

    def tryTwoStepLogin(login_data):
        if login_data["two_step_url"] is not None:
            login_data["two_step_security_code"] = input("enter two-step security code: ")

            # Send the security code back to GOG
            args={"second_step_authentication[token][letter_1]": login_data["two_step_security_code"][0],
                  "second_step_authentication[token][letter_2]": login_data["two_step_security_code"][1],
                  "second_step_authentication[token][letter_3]": login_data["two_step_security_code"][2],
                  "second_step_authentication[token][letter_4]": login_data["two_step_security_code"][3],
                  "second_step_authentication[send]": "",
                  "second_step_authentication[_token]": login_data["two_step_token"]}
            with request(login_data["two_step_url"], delay=0, args=args) as page:
                if "on_login_success" in page.geturl():
                    login_data["login_success"] = True

    global_cookies.clear()

    user = input("Username: ")
    passwd = getpass.getpass()
    login_data = {"user": user, "passwd": passwd, "auth_url": None, "login_token": None, "two_step_url": None, "two_step_token": None, "two_step_security_code": None, "login_success": False}

    fetchAuthURL(login_data)
    fetchLoginToken(login_data)
    tryBasicLogin(login_data)
    tryTwoStepLogin(login_data)

    if login_data["login_success"]:
        info("login successful!")
        global_cookies.save()
    else:
        error("login failed, verify your username/password and try again.")


def cmd_update(os_list, lang_list, media_type, downloadpatches):
    def cmd_update_movies(lang_list):
        return

    def cmd_update_games(os_list, lang_list, downloadpatches):
        def fetch_game_list():
            def fetch_games():
                def fetch_total_pages():
                    url = (GOG_ACCOUNT_URL + "/getFilteredProducts" + "?" + urlencode({"mediaType": GOG_MEDIA_TYPE_GAME, "sortBy": "title"}))
                    with request(url) as data_request:
                        return range(1, json.load(READER(data_request))["totalPages"]+1)

                games = []
                for i in fetch_total_pages():
                    url = (GOG_ACCOUNT_URL + "/getFilteredProducts" + "?" + urlencode({"mediaType": GOG_MEDIA_TYPE_GAME, "sortBy": "title", "page": str(i)}))
                    with request(url) as data_request:
                        games.extend(json.load(READER(data_request))["products"])

                return games

            def append(games, game):
                id = game["id"]
                path = game["slug"]
                title = cleanString(game["title"])
                image_url = "http:" + game["image"].replace("-1", "").replace("-2", "").replace("-3", "").replace("-4", "") + ".jpg"

                games.append({'id':id, 'path':path, 'title':title, 'image_url':image_url})

            games = []
            for game in fetch_games():
                if (game.get("isHidden", False) is True) or (game["id"] in EXCLUDED_IDS):
                    continue

                append(games, game)

            return games;

        def fetch_file_info(url, fetch_name=True, fetch_md5=False):
            name = None
            size = None
            md5 = None

            try:
                with request(url, byte_range=(0, 0), check_headers=("Content-Range", "0-0/[0-9]+")) as file_page:
                    size = int(file_page.headers["Content-Range"].split("/")[-1])

                    if fetch_name:
                        name = unquote(urlparse(file_page.geturl()).path.split("/")[-1])

                    if fetch_md5:
                        with request(file_page.geturl().replace("?", ".xml?")) as md5_page:
                            md5 = xml.etree.ElementTree.parse(md5_page).getroot().attrib["md5"]

            except HTTPError as e:
                if e.code == 404:
                    pass

            except Exception:
                pass

            return name, size, md5

        def fetch_game_details(os_list, lang_list, downloadpatches, remoteBaseGames, baseGamesInfo):
            def fetch_game_downloads(remoteBaseGame, remoteGameInfo, backupGameInfo):
                def add_game_download_if_necessary(download):
                    href = GOG_HOME_URL + download["manualUrl"]
                    version = download["version"]

                    if backupGameInfo is not None:
                        backupGame_idx = item_checkdb(href, backupGameInfo["downloads"], "href")
                        if (backupGame_idx is not None) and (version == backupGameInfo["downloads"][backupGame_idx]["version"]):
                            remoteBaseGame["downloads"].append(backupGameInfo["downloads"][backupGame_idx])
                            info("{:>60} - {}".format("backup", href))
                            return

                    (name, size, md5) = fetch_file_info(href, fetch_md5=True)
                    if (name is not None) and (size is not None) and (md5 is not None):
                        game_download = {}
                        game_download["able"] = True if ((downloadpatches) or (href.find("patch") == -1)) else False
                        game_download["desc"] = cleanString(download["name"])
                        game_download["name"] = name
                        game_download["version"] = version
                        game_download["size"] = size
                        game_download["md5"] = md5
                        game_download["href"] = href

                        remoteBaseGame["downloads"].append(game_download)
                        info("{:>60} - {}".format("remote", href))

                remote_downloads = dict(remoteGameInfo["downloads"])
                for lang in lang_list:
                    if lang in remote_downloads:
                        for os in os_list:
                            if os in remote_downloads[lang]:
                                for download in remote_downloads[lang][os]:
                                    add_game_download_if_necessary(download)

            def fetch_game_extras(remoteBaseGame, remoteGameInfo, backupGameInfo, cover=False):
                def add_game_extra_if_necessary(extra):
                    if backupGameInfo is not None:
                        backupGame_idx = item_checkdb(extra["href"], backupGameInfo["extras"], "href")
                        if backupGame_idx is not None:
                            remoteBaseGame["extras"].append(backupGameInfo["extras"][backupGame_idx])
                            info("{:>60} - {}".format("backup", extra["href"]))
                            return

                    if extra["name"] == "cover":
                        name = extra["filename"]
                        (_, size, _) = fetch_file_info(extra["href"], fetch_name=False)
                    else:
                        (name, size, _) = fetch_file_info(extra["href"])

                    if (name is not None) and (size is not None):
                        game_extra = {}
                        game_extra["able"] = bool(extra.get("info"))
                        game_extra["desc"] = extra["name"]
                        game_extra["name"] = name
                        game_extra["size"] = size
                        game_extra["href"] = extra["href"]

                        remoteBaseGame["extras"].append(game_extra)
                        info("{:>60} - {}".format("remote", extra["href"]))

                if cover:
                    add_game_extra_if_necessary({"name":"cover", "href":remoteBaseGame.pop("image_url"), "filename":IMAGE_FILENAME, "info":1})

                for extra in remoteGameInfo["extras"]:
                    extra["href"] = GOG_HOME_URL + extra["manualUrl"]
                    add_game_extra_if_necessary(extra)

            def fetch_game_dlcs(remoteBaseGame, remoteGameInfo, backupGameInfo):
                for dlc in remoteGameInfo["dlcs"]:
                    if bool(dlc["downloads"]):
                        fetch_game_downloads(remoteBaseGame, dlc, backupGameInfo)

                        game_dlc = {}
                        game_dlc["title"] = dlc["title"]
                        if bool(dlc.get("cdKey")):
                            game_dlc["serial"] = dlc["cdKey"]

                        remoteBaseGame["dlcs"] = remoteBaseGame.get("dlcs", [])
                        remoteBaseGame["dlcs"].append(game_dlc)

                    fetch_game_extras(remoteBaseGame, dlc, backupGameInfo)

            items_count = len(remoteBaseGames)
            info("found %d games !!%s" % (items_count, "!" * int(items_count / 100)))

            i = 1
            global GAMES
            GAMES = []
            print_padding = len(str(items_count))
            for remoteBaseGame in sorted(remoteBaseGames, key=lambda remoteBaseGame: remoteBaseGame["title"]):
                header = "(%*d / %d) fetching game details" % (print_padding, i, items_count)
                info("{:>60} - {}".format(header, remoteBaseGame["title"]))
                i += 1

                api_url = GOG_ACCOUNT_URL + "/gameDetails/{}.json".format(remoteBaseGame["id"])
                with request(api_url) as data_request:
                    remoteGameInfo = json.load(READER(data_request))

                    if bool(remoteGameInfo["cdKey"]):
                        remoteBaseGame["serial"] = remoteGameInfo["cdKey"]

                    remoteBaseGame["downloads"] = []
                    remoteBaseGame["extras"] = []

                    item_idx = item_checkdb(remoteBaseGame["id"], baseGamesInfo, "id")
                    backupGameInfo = None if item_idx is None else baseGamesInfo[item_idx]

                    fetch_game_downloads(remoteBaseGame, remoteGameInfo, backupGameInfo)
                    fetch_game_extras(remoteBaseGame, remoteGameInfo, backupGameInfo, cover=True)
                    fetch_game_dlcs(remoteBaseGame, remoteGameInfo, backupGameInfo)

                    GAMES.append(remoteBaseGame)

                info('')

        global_cookies.load()
        remoteBaseGames = fetch_game_list()

        if len(remoteBaseGames) == 0:
            warn("nothing to do")
        else:
            fetch_game_details(os_list, lang_list, downloadpatches, remoteBaseGames, GAMES)

    if media_type == GOG_MEDIA_TYPE_ALL:
        cmd_update_games(os_list, lang_list, downloadpatches)
        cmd_update_movies(lang_list)

    elif media_type == GOG_MEDIA_TYPE_GAME:
        cmd_update_games(os_list, lang_list, downloadpatches)

    elif media_type == GOG_MEDIA_TYPE_MOVIE:
        cmd_update_movies(lang_list)

    info("-" * 60)


def cmd_clean(cleandir):
    info("cleaning local directories within '{}'".format(cleandir))

    expectedFolders = {}
    for backupProduct in GAMES:
        expectedFiles = expectedFolders[backupProduct["path"]] = []
        for item in (backupProduct["downloads"] + backupProduct["extras"]):
            if item.get("able", True):
                expectedFiles.append(item["name"])

    with os.scandir(cleandir) as baseFolderIterator:
        for folderEntry in baseFolderIterator:
            if folderEntry.is_dir():
                if folderEntry.name not in expectedFolders:
                    info("{:>60} - {}".format("deleting", folderEntry.path))
                    shutil.rmtree(folderEntry.path)

                else:
                    with os.scandir(folderEntry) as productFolderIterator:
                        for fileEntry in productFolderIterator:
                            if (fileEntry.is_file()) and (fileEntry.name not in expectedFolders[folderEntry.name]):
                                info("{:>60} - {}".format("deleting", fileEntry.path))
                                os.remove(fileEntry.path)

    info("-" * 60)

def cmd_download(savedir):
    info("downloading pending files within '{}'".format(savedir))

    def fillWorkQueue(backupProductsInfo):
        def makeHomeDir(path):
            productFolder = os.path.join(savedir, path)

            if not os.path.isdir(productFolder):
                os.makedirs(productFolder)

            return productFolder

        works = Queue()
        sizes = {}

        def addItemIfNecessary(productFolder, item):
            if item.get("able", True):
                itemFile = os.path.join(productFolder, item["name"])

                if os.path.isfile(itemFile):
                    if item["size"] == os.path.getsize(itemFile):
                        return

                    if item["size"] < os.path.getsize(itemFile):
                        os.remove(path)
                        error("{:>60} - {}".format("FAIL, has incorrect size.", item["name"]))

                    else:
                        works.put((item["href"], os.path.getsize(itemFile), item["size"] - 1, itemFile, item["size"], item.get("md5")))
                        sizes[itemFile] = item["size"] - os.path.getsize(itemFile)
                        info("{:>60} - {}".format("add to download", item["name"]))

                else:
                    works.put((item["href"], 0, item["size"] - 1, itemFile, item["size"], item.get("md5")))
                    sizes[itemFile] = item["size"]
                    info("{:>60} - {}".format("add to download", item["name"]))

        for backupProductInfo in sorted(backupProductsInfo, key=lambda item: item["title"]):
            info("{:>60}".format(backupProductInfo["title"]))
            productFolder = makeHomeDir(backupProductInfo["path"])

            for item in backupProductInfo["downloads"] + backupProductInfo["extras"]:
                addItemIfNecessary(productFolder, item)

        return works, sizes

    def downloadPendingItems(works, sizes):
        def openFileDescriptor(name, bufsize=4 * 1024, append=False):
            flags = os.O_WRONLY | os.O_CREAT | os.O_BINARY # windows
            if (append):
                return os.fdopen(os.open(name, flags, 0o666), "ab", bufsize)
            else:
                return os.fdopen(os.open(name, flags, 0o666), "wb", bufsize)

        def showDownloadInfo(path, start, sizes, clocks):
            def calculateRemainingTime(totalRemainingSize, clocks):
                elapsedX15 = 6 * clocks[0] - sum(clocks)

                downloadSize = HTTP_DOWNLOAD_SPEED * 1024 * 1024
                downloadSpeed = downloadSize * 15 / (15 if elapsedX15 == 0 else elapsedX15)

                hours, rem = divmod(totalRemainingSize / downloadSpeed, 3600)
                minutes, seconds = divmod(rem, 60)
                return "{:02}:{:02}:{:02}".format(int(hours), int(minutes), int(seconds))

            totalRemainingSize = pretty_size(sum(sizes.values()))
            totalRemainingTime = calculateRemainingTime(sum(sizes.values()), clocks)

            fileDownloadedSize = pretty_size(start)
            fileRemainingSize = pretty_size(sizes[path])
            fileName = os.path.split(path)[1]

            info("Total: {:>10} ({}) | File: {:>10} / {:>10} - {}".format(totalRemainingSize, totalRemainingTime, fileDownloadedSize, fileRemainingSize, fileName))

        def verifyOK(path, size, md5):
            def hashfile(afile, blocksize=65536):
                afile = open(afile, "rb")
                hasher = hashlib.md5()
                buf = afile.read(blocksize)
                while len(buf) > 0:
                    hasher.update(buf)
                    buf = afile.read(blocksize)

                return hasher.hexdigest()

            info("{:>60} - {}".format("verifying", os.path.split(path)[1]))

            if (size != os.path.getsize(path)):
                error("{:>60} - {}".format("mismatched file size", os.path.split(path)[1]))
                info('')
                return False

            if ((md5 is not None) and (md5 != hashfile(path))):
                error("{:>60} - {}".format("mismatched md5", os.path.split(path)[1]))
                info('')
                return False

            info('')
            return True

        while not works.empty():
            try:
                (url, start, end, path, size, md5) = works.get()

                with request(url, byte_range=(start, end), check_headers=("Content-Range", "{}-{}/{}".format(start, end, size))) as page:
                    with openFileDescriptor(path, append = start!=0) as out:
                        hasRead = True
                        clocks = time.time(), time.time()-1, time.time()-2, time.time()-3, time.time()-4, time.time()-5
                        while hasRead:
                            showDownloadInfo(path, start, sizes, clocks)
                            clocks = time.time(), clocks[0], clocks[1], clocks[2], clocks[3], clocks[4]
                            buf = page.read(HTTP_DOWNLOAD_SPEED * 1024 * 1024)
                            out.write(buf)
                            start += len(buf)
                            hasRead = len(buf)
                            sizes[path] -= len(buf)

                if not(verifyOK(path, size, md5)):
                    works.put((url, 0, end, path, size, md5))
                    sizes[path] = size
                    os.remove(path)
                    info("   redownload   %s" % game_item.name)

            except Exception as e:
                info("Exception")
                error(e)
                works.put((url, start, end, path, size, md5))
                time.sleep(1)

    global_cookies.load()
    (works, sizes) = fillWorkQueue(GAMES)
    downloadPendingItems(works, sizes)


if __name__ == "__main__":
    def main(args):
        start_time = datetime.datetime.now()

        if args.cmd == "login":
            cmd_login()
            return  # no need to see time stats

        elif args.cmd == "update":
            load_manifest()
            cmd_update(args.os, args.lang, args.type, args.downloadpatches)
            save_manifest()
            cmd_clean(args.savedir)
            cmd_download(args.savedir)

        info("-" * 60)
        info("total time: %s" % (datetime.datetime.now() - start_time))

    def process_argv(argv):
        p1 = argparse.ArgumentParser(description="%s (%s)" % (__appname__, __url__), add_help=False)
        sp1 = p1.add_subparsers(help="commands", dest="cmd", title="commands")

        g1 = sp1.add_parser("login", help="Login to GOG and save a local copy of your authenticated cookie")

        g1 = sp1.add_parser("update", help="Update locally saved game manifest from GOG server")
        g1.add_argument("-os", action="store", help="operating system(s)", nargs="*", default=DEFAULT_OS_LIST)
        g1.add_argument("-lang", action="store", help="game language(s)", nargs="*", default=DEFAULT_LANG_LIST)
        g1.add_argument("-type", action="store", help="media type", nargs="?", default=GOG_MEDIA_TYPE_ALL)
        g1.add_argument("-downloadpatches", action="store_true", help="only games installers")
        g1.add_argument("-no-cover", action="store_true", help="don't download covers")
        g1.add_argument("savedir", action="store", help="directory to save downloads to", nargs="?", default=".")

        g1 = p1.add_argument_group("other")
        g1.add_argument("-h", "--help", action="help", help="show help message and exit")
        g1.add_argument("-v", "--version", action="version", help="show version number and exit", version="%s (version %s)" % (__appname__, __version__))

        return p1.parse_args(argv[1:])

    try:
        main(process_argv(sys.argv))
        info("exiting...")

    except KeyboardInterrupt:
        info("exiting...")
        sys.exit(1)

    except SystemExit:
        raise

    except:
        log_exception("fatal...")
        sys.exit(1)
