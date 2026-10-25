# Stars Multiplayer
# Made by herixd3
# Copyright (c) 2026 herixd3. All rights reserved.
bl_info = {
    "name": "Stars Multiplayer",
    "author": "herixd3",
    "version": (0, 9, 1),
    "blender": (3, 4, 0),
    "location": "3D Viewport > Sidebar (N) > Stars",
    "description": "Live multiplayer rooms: shared scene, smooth colored cursors, host-controlled Ctrl+Z, host can kick. No external server.",
    "category": "3D View",
}

import base64
import json
import math
import os
import queue
import re
import secrets
import socket
import struct
import threading
import time
import urllib.parse
import urllib.request
import uuid

import blf
import bmesh
import bpy
import gpu
from bpy.props import (BoolProperty, CollectionProperty, EnumProperty,
                       FloatVectorProperty, IntProperty, StringProperty)
from bpy.types import Operator, Panel, PropertyGroup
from bpy_extras import view3d_utils
from gpu_extras.batch import batch_for_shader
from mathutils import Vector

DEFAULT_PORT = 9876

# Room settings: only the host can change these, everyone in the room follows them.
# To add another host-only setting: add it here, add a row in tab_settings, and read S["rs"]["name"].
ROOM_DEFAULTS = {"undo": "OWN", "edit": True}   # undo: "OWN" / "GLOBAL". edit: can guests change the scene?
HOST_ONLY = {"rs", "kick"}        # message types the host refuses to relay when a guest sends them
# message types that change the scene: the host drops these from guests when editing is turned off
EDIT_TYPES = {"add", "del", "x", "m", "pr", "md", "mat", "col", "sc", "act", "ud", "req"}
AVATAR_MAX = 64                   # pictures are shrunk to fit this many pixels
AVATAR_PX = 40                    # size of a picture on screen
AVATAR_MAX_FILE = 10 * 1024 * 1024
# Public rooms are announced on a free public message board (ntfy.sh) so people anywhere can find them.
DIRECTORY = "https://ntfy.sh/stars-multiplayer-rooms-v1"
PUB_EVERY = 60                    # seconds between "I'm still here" announcements
PUB_WINDOW = 150                  # a listing older than this is considered gone
UNDO_GAP = 0.4                    # seconds of quiet that end one undo step
MAX_UNDO = 100                    # how many of your own steps are remembered
SMOOTH_TAU = 0.07                 # cursor smoothing, seconds (bigger = smoother but laggier)

# ----------------------------------------------------------------------------
# Networking (plain TCP, newline-delimited JSON, stdlib only)
# The room "host" is whoever clicks Host Room. Everyone else connects straight
# to the host using the room code. The host relays messages between everyone.
# ----------------------------------------------------------------------------


class Net:
    def __init__(self):
        self.q = queue.Queue()
        self.conns = []
        self.lock = threading.Lock()
        self.server = None
        self.is_host = False
        self.running = False
        self.hellos = {}
        self.by_id = {}
        self.info = {}
        self.guest_edit = True  # host only: may guests change the scene?
        self.pub_evt = threading.Event()  # wakes the announcer when "public" is switched
        self._pubip = ""
        self.relay = None  # Easy connect tunnel (host only)

    def start_host(self, port):
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        s.bind(("0.0.0.0", port))
        s.listen(8)
        s.settimeout(0.5)
        self.server = s
        self.is_host = True
        self.running = True
        threading.Thread(target=self._accept, daemon=True).start()
        threading.Thread(target=self._discover, daemon=True).start()
        threading.Thread(target=self._publish, daemon=True).start()

    def _publish(self):
        # While the room is public, announce it on the public board (and say so when it stops).
        listed = False
        while self.running:
            i = self.info
            if i.get("public") and i.get("ip"):
                ip = i.get("pub_host") or i["ip"]
                port = i.get("pub_port") or i.get("port", DEFAULT_PORT)
                if not i.get("pub_host") and ip_tag(ip) in ("same Wi-Fi / LAN", "this computer only"):
                    if not self._pubip:
                        try:
                            self._pubip = urllib.request.urlopen("https://api.ipify.org", timeout=5).read().decode().strip()
                        except Exception:
                            pass
                    ip = self._pubip or ip
                if dir_post({"room": i.get("room", ""), "short": i.get("short", ""),
                             "players": i.get("players", 1), "ip": ip, "port": port}):
                    listed = True
            elif listed:
                dir_post({"short": i.get("short", ""), "closed": True})
                listed = False
            self.pub_evt.wait(PUB_EVERY)
            self.pub_evt.clear()
        if listed:
            dir_post({"short": self.info.get("short", ""), "closed": True})

    def start_client(self, host, port):
        c = socket.create_connection((host, port), timeout=6)
        c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        c.settimeout(10.0)
        self.is_host = False
        self.running = True
        with self.lock:
            self.conns.append(c)
        threading.Thread(target=self._reader, args=(c,), daemon=True).start()

    def stop(self):
        self.running = False
        self.pub_evt.set()
        if self.relay:
            self.relay.stop()
        with self.lock:
            conns = list(self.conns)
            self.conns.clear()
        for c in conns:
            try:
                c.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                c.close()
            except Exception:
                pass
        if self.server:
            try:
                self.server.close()
            except Exception:
                pass
            self.server = None

    def _discover(self):
        # Answers "who is hosting?" questions from other Blenders on the same network.
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind(("", DISC_PORT))
        except OSError:
            s.close()
            return
        s.settimeout(0.5)
        while self.running:
            try:
                data, addr = s.recvfrom(256)
            except socket.timeout:
                continue
            except OSError:
                break
            if not data.startswith(b"STARS?"):
                continue
            want = data[6:].decode(errors="ignore").strip().upper()
            i = self.info
            ok = (want == i.get("short")) if want else bool(i.get("public"))
            if ok:
                reply = {"room": i.get("room", ""), "short": i.get("short", ""),
                         "players": i.get("players", 1), "port": i.get("port", DEFAULT_PORT)}
                try:
                    s.sendto(json.dumps(reply).encode(), addr)
                except OSError:
                    pass
        s.close()

    def _accept(self):
        while self.running:
            try:
                c, _ = self.server.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            c.settimeout(10.0)
            with self.lock:
                self.conns.append(c)
            threading.Thread(target=self._reader, args=(c,), daemon=True).start()

    def _reader(self, conn):
        buf = b""
        pid = None
        ok = not self.is_host  # on the host, a guest must send the right room code before anything else counts
        try:
            while self.running:
                try:
                    data = conn.recv(1 << 20)
                except socket.timeout:
                    continue
                if not data:
                    break
                buf += data
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    if not line.strip():
                        continue
                    msg = json.loads(line)
                    if self.is_host:
                        if not ok:
                            code = str(msg.get("code", "")).strip().upper()
                            if msg.get("t") == "hello" and ((code and code == str(self.info.get("code", "")).upper())
                                                            or self.info.get("public")):  # public room: no code needed
                                ok = True
                                msg.pop("code", None)  # never pass the code on to other guests
                            else:
                                self._send_to(conn, (json.dumps({"t": "deny", "why": "Wrong room code"}) + "\n").encode())
                                return
                        mt = msg.get("t")
                        if mt in HOST_ONLY:
                            continue  # guests can't change room settings or kick people
                        if mt in EDIT_TYPES and not self.guest_edit:
                            continue  # the host turned editing off for guests
                        if mt == "resync":
                            if pid:
                                msg["id"] = pid
                                self.q.put(msg)  # only the host needs this one
                            continue
                        if mt in ("av", "prof") and pid:
                            msg["id"] = pid  # can't pretend to be someone else
                            h = self.hellos.get(pid)
                            if h is not None:  # late joiners get the new picture / name / color
                                if mt == "av":
                                    h["av"] = msg.get("av")
                                else:
                                    h["name"] = str(msg.get("name") or "Player")[:32]
                                    if isinstance(msg.get("color"), list) and len(msg["color"]) == 3:
                                        h["color"] = msg["color"]
                        if msg.get("t") == "hello":
                            pid = msg.get("id")
                            self.by_id[pid] = conn
                            for h in list(self.hellos.values()):
                                self._send_to(conn, (json.dumps(h) + "\n").encode())
                            self.hellos[pid] = msg
                        self.send(msg, skip=conn)
                    self.q.put(msg)
        except Exception as e:  # noqa
            self.q.put({"t": "_err", "e": str(e)})
        finally:
            self._drop(conn)
            if self.is_host:
                if pid:
                    self.hellos.pop(pid, None)
                    bye = {"t": "bye", "id": pid}
                    self.send(bye)
                    self.q.put(bye)
            elif self.running:
                self.q.put({"t": "_closed"})

    def _drop(self, c):
        with self.lock:
            if c in self.conns:
                self.conns.remove(c)
        for k, v in list(self.by_id.items()):
            if v is c:
                self.by_id.pop(k, None)
        try:
            c.shutdown(socket.SHUT_RDWR)  # wakes the reader thread and sends FIN right away
        except Exception:
            pass
        try:
            c.close()
        except Exception:
            pass

    def _send_to(self, c, data):
        try:
            c.sendall(data)
        except Exception:
            self._drop(c)

    def send_to_id(self, pid, msg):
        c = self.by_id.get(pid)
        if c:
            self._send_to(c, (json.dumps(msg, separators=(",", ":")) + "\n").encode())

    def kick(self, pid):
        c = self.by_id.get(pid)
        if c:
            self._send_to(c, (json.dumps({"t": "kick"}) + "\n").encode())
            time.sleep(0.05)
            self._drop(c)

    def send(self, msg, skip=None):
        data = (json.dumps(msg, separators=(",", ":")) + "\n").encode()
        with self.lock:
            conns = list(self.conns)
        for c in conns:
            if c is not skip:
                self._send_to(c, data)


# ----------------------------------------------------------------------------
# IPs and room codes
# ----------------------------------------------------------------------------

def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


def gen_room_code():
    return "".join(secrets.choice("ABCDEFGHJKMNPQRSTUVWXYZ23456789") for _ in range(6))


def upnp_open(port, lan):
    """Ask the router (UPnP) to forward TCP `port` to this computer. Returns the router's public IP if known."""
    ssdp = ("M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\n"
            "MAN: \"ssdp:discover\"\r\nMX: 2\r\n"
            "ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n").encode()
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(3)
    try:
        s.sendto(ssdp, ("239.255.255.250", 1900))
        data = s.recvfrom(4096)[0].decode(errors="ignore")
    except socket.timeout:
        raise RuntimeError("no UPnP router found")
    finally:
        s.close()
    m = re.search(r"(?im)^location:\s*(\S+)", data)
    if not m:
        raise RuntimeError("router gave no address")
    loc = m.group(1)
    xml = urllib.request.urlopen(loc, timeout=4).read().decode(errors="ignore")
    m = re.search(r"<serviceType>(urn:schemas-upnp-org:service:WAN(?:IP|PPP)Connection:\d)</serviceType>"
                  r".*?<controlURL>(.*?)</controlURL>", xml, re.S)
    if not m:
        raise RuntimeError("router has no port-forward service")
    st, ctrl = m.group(1), urllib.parse.urljoin(loc, m.group(2).strip())

    def soap(action, args):
        body = ('<?xml version="1.0"?><s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
                's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body>'
                '<u:%s xmlns:u="%s">%s</u:%s></s:Body></s:Envelope>') % (action, st, args, action)
        req = urllib.request.Request(ctrl, data=body.encode(), headers={
            "Content-Type": 'text/xml; charset="utf-8"', "SOAPAction": '"%s#%s"' % (st, action)})
        return urllib.request.urlopen(req, timeout=5).read().decode(errors="ignore")

    soap("AddPortMapping",
         "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort>"
         "<NewProtocol>TCP</NewProtocol><NewInternalPort>%d</NewInternalPort>"
         "<NewInternalClient>%s</NewInternalClient><NewEnabled>1</NewEnabled>"
         "<NewPortMappingDescription>Stars Multiplayer</NewPortMappingDescription>"
         "<NewLeaseDuration>0</NewLeaseDuration>" % (port, port, lan))
    try:
        r = soap("GetExternalIPAddress", "")
        m = re.search(r"<NewExternalIPAddress>(.*?)</NewExternalIPAddress>", r)
        return m.group(1).strip() if m else ""
    except Exception:
        return ""


def ip_tag(ip):
    try:
        a = [int(x) for x in ip.split(".")]
    except Exception:
        return ""
    if a[0] == 127:
        return "this computer only"
    if a[0] == 100 and 64 <= a[1] <= 127:
        return "VPN (Tailscale)"
    if a[0] == 10 or (a[0] == 192 and a[1] == 168) or (a[0] == 172 and 16 <= a[1] <= 31):
        return "same Wi-Fi / LAN"
    return "public"


def local_ips():
    found = []
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            found.append(info[4][0])
    except Exception:
        pass
    found.append(lan_ip())
    out = []
    for ip in found:
        if ip not in out and not ip.startswith("127.") and not ip.startswith("169.254."):
            out.append(ip)
    return [(ip, ip_tag(ip)) for ip in out] or [("127.0.0.1", ip_tag("127.0.0.1"))]


DISC_PORT = 9877
SCAN = {"rooms": [], "net_rooms": [], "err": "", "busy": False, "done": False}
SHORT_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"


def gen_short():
    import random
    return "".join(random.choice(SHORT_CHARS) for _ in range(4))


def scan_rooms(code="", timeout=1.2):
    # Ask everyone on the network (and this computer) who is hosting.
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
    s.settimeout(0.3)
    q = ("STARS?" + code).encode()
    targets = ["255.255.255.255", "127.0.0.1"]
    ip = lan_ip()
    if ip.count(".") == 3:
        targets.append(ip.rsplit(".", 1)[0] + ".255")
    for t in targets:
        try:
            s.sendto(q, (t, DISC_PORT))
        except OSError:
            pass
    found = {}
    end = time.time() + timeout
    while time.time() < end:
        try:
            data, addr = s.recvfrom(2048)
        except socket.timeout:
            continue
        except OSError:
            break
        try:
            info = json.loads(data)
            info["ip"] = addr[0]
            key = info.get("short") or (addr[0], info.get("port"))
        except Exception:
            continue
        old = found.get(key)
        if old is None or (old["ip"].startswith("127.") and not addr[0].startswith("127.")):
            found[key] = info
    s.close()
    return list(found.values())


def start_scan():
    if SCAN["busy"]:
        return
    SCAN["busy"] = True

    def work():
        try:
            rooms = scan_rooms(timeout=1.5)
        except Exception:
            rooms = []
        SCAN["rooms"] = rooms
        try:
            SCAN["net_rooms"] = fetch_public()
            SCAN["err"] = ""
        except Exception as e:
            SCAN["net_rooms"] = []
            SCAN["err"] = str(e)[:60]
        SCAN["busy"] = False
        SCAN["done"] = True
    threading.Thread(target=work, daemon=True).start()


def make_code(host, port):
    parts = host.split(".")
    if len(parts) == 4 and all(p.isdigit() and 0 <= int(p) <= 255 for p in parts):
        raw = bytes(int(p) for p in parts) + struct.pack(">H", port)
        c = base64.b32encode(raw).decode().rstrip("=")
        return c[:5] + "-" + c[5:]
    return "%s:%d" % (host, port)


def parse_target(text):
    t = text.strip()
    if ":" in t:
        h, p = t.rsplit(":", 1)
        return h.strip(), int(p)
    raw = t.replace("-", "").replace(" ", "").upper()
    if len(raw) <= 6:  # short LAN code like K7QP
        rooms = scan_rooms(code=raw, timeout=1.2)
        if not rooms:
            raise ValueError("no room with that code found on your network")
        return rooms[0]["ip"], rooms[0]["port"]
    raw += "=" * (-len(raw) % 8)
    b = base64.b32decode(raw)
    return ".".join(str(x) for x in b[:4]), struct.unpack(">H", b[4:6])[0]


# ----------------------------------------------------------------------------
# Player pictures
# You pick a PNG; it is shrunk to at most 64x64 and sent to everyone as raw RGBA bytes.
# ----------------------------------------------------------------------------

AVATAR = {"av": None}   # my own picture, kept between rooms: {"w", "h", "d": base64 RGBA8}


def avatar_ok(av):
    try:
        w, h = int(av["w"]), int(av["h"])
        return (1 <= w <= AVATAR_MAX and 1 <= h <= AVATAR_MAX
                and len(base64.b64decode(av["d"])) == w * h * 4)
    except Exception:
        return False


def clean_av(av):
    return {"w": int(av["w"]), "h": int(av["h"]), "d": av["d"]} if av and avatar_ok(av) else None


def _srgb(v):
    return v * 12.92 if v <= 0.0031308 else 1.055 * (v ** (1 / 2.4)) - 0.055


def make_avatar(path):
    path = bpy.path.abspath(path)
    if not path.lower().endswith(".png"):
        raise ValueError("it has to be a .png file")
    if os.path.getsize(path) > AVATAR_MAX_FILE:
        raise ValueError("file is too big (max 10 MB)")
    img = bpy.data.images.load(path, check_existing=False)
    try:
        w, h = img.size
        if w < 1 or h < 1:
            raise ValueError("couldn't read the image")
        if max(w, h) > AVATAR_MAX:
            k = AVATAR_MAX / max(w, h)
            img.scale(max(1, round(w * k)), max(1, round(h * k)))
            w, h = img.size
        px = img.pixels[:]
        if len(px) != w * h * 4:
            raise ValueError("unsupported image")
        lin = img.is_float
        out = bytearray(len(px))
        for i, v in enumerate(px):
            if lin and i % 4 != 3:
                v = _srgb(max(v, 0.0))
            out[i] = int(min(1.0, max(0.0, v)) * 255 + 0.5)
        return {"w": w, "h": h, "d": base64.b64encode(bytes(out)).decode()}
    finally:
        bpy.data.images.remove(img)


class Relay:
    """Easy connect: asks a free public 'bore' relay (bore.pub) for a public address that leads to this
    computer, so nobody has to open a port. Speaks bore's tiny protocol (JSON messages ending in a 0 byte)."""

    def __init__(self, server, local_port, control_port=7835):
        self.server, self.local_port, self.control_port = server, local_port, control_port
        self.ctl = None
        self.alive = False
        self.remote_port = 0

    @staticmethod
    def _read_msg(sock, buf):
        while b"\0" not in buf:
            data = sock.recv(4096)
            if not data:
                raise ConnectionError("relay closed the connection")
            buf += data
        raw, buf = buf.split(b"\0", 1)
        return json.loads(raw), buf

    def start(self):
        s = socket.create_connection((self.server, self.control_port), timeout=8)
        try:
            s.settimeout(8)
            s.sendall(b'{"Hello":0}\0')
            msg, buf = self._read_msg(s, b"")
            if isinstance(msg, dict) and "Hello" in msg:
                self.remote_port = int(msg["Hello"])
            elif isinstance(msg, dict) and "Error" in msg:
                raise RuntimeError("relay said: %s" % msg["Error"])
            elif isinstance(msg, dict) and "Challenge" in msg:
                raise RuntimeError("that relay needs a password")
            else:
                raise RuntimeError("unexpected reply from relay")
        except Exception:
            s.close()
            raise
        self.ctl = s
        self.alive = True
        s.settimeout(15)   # the relay pings every half second; silence means it is gone
        threading.Thread(target=self._listen, args=(s, buf), daemon=True).start()
        return self.remote_port

    def stop(self):
        self.alive = False
        try:
            self.ctl.close()
        except Exception:
            pass

    def _listen(self, s, buf):
        try:
            while self.alive:
                msg, buf = self._read_msg(s, buf)
                if isinstance(msg, dict) and "Connection" in msg:
                    threading.Thread(target=self._handle, args=(str(msg["Connection"]),), daemon=True).start()
        except Exception:
            pass
        self.alive = False

    def _handle(self, cid):
        r = l = None
        try:
            r = socket.create_connection((self.server, self.control_port), timeout=8)
            r.sendall(json.dumps({"Accept": cid}, separators=(",", ":")).encode() + b"\0")
            l = socket.create_connection(("127.0.0.1", self.local_port), timeout=5)
            for x in (r, l):
                x.settimeout(None)
                x.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except Exception:
            for x in (r, l):
                try:
                    x.close()
                except Exception:
                    pass
            return
        threading.Thread(target=self._pipe, args=(l, r), daemon=True).start()
        self._pipe(r, l)

    @staticmethod
    def _pipe(src, dst):
        try:
            while True:
                d = src.recv(65536)
                if not d:
                    break
                dst.sendall(d)
        except Exception:
            pass
        for x in (src, dst):
            try:
                x.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                x.close()
            except Exception:
                pass


def resolve_host(host):
    """Turn a name like bore.pub into an IP address, even when this computer's DNS is broken or blocked."""
    if re.fullmatch(r"[0-9.]+", host):
        return host
    try:
        return socket.gethostbyname(host)
    except OSError:
        pass
    for url, hdr in (("https://1.1.1.1/dns-query?name=%s&type=A" % host, {"accept": "application/dns-json"}),
                     ("https://8.8.8.8/resolve?name=%s&type=A" % host, {})):
        try:
            req = urllib.request.Request(url, headers=dict(hdr, **{"User-Agent": "StarsMultiplayer"}))
            data = json.loads(urllib.request.urlopen(req, timeout=5).read().decode())
            for a in data.get("Answer", []):
                if a.get("type") == 1:
                    return a["data"]
        except Exception:
            continue
    return host


def start_relay(net, server, port):
    """Open the Easy connect tunnel in the background (Blender keeps running)."""
    def work():
        server_ip = resolve_host(server)   # friends get a plain IP, so they never need DNS for it
        relay = Relay(server_ip, port)
        try:
            rp = relay.start()
        except Exception as e:
            if S["net"] is net:
                S["relay_status"] = "Easy connect failed: %s" % str(e)[:60]
            SCAN["done"] = True
            return
        if S["net"] is not net or not net.running:
            relay.stop()
            return
        net.relay = relay
        net.info["pub_host"], net.info["pub_port"] = server_ip, rp
        if not S["lan"]:
            S["lan"] = (S["addr"], S["port"])
        S["addr"], S["port"] = server_ip, rp
        S["relay_status"] = "Easy connect: on"
        net.pub_evt.set()
        SCAN["done"] = True   # makes the panel redraw
    threading.Thread(target=work, daemon=True).start()


def dir_post(d):
    try:
        req = urllib.request.Request(DIRECTORY, data=json.dumps(d, separators=(",", ":")).encode(),
                                     method="POST", headers={"User-Agent": "StarsMultiplayer"})
        urllib.request.urlopen(req, timeout=6).read()
        return True
    except Exception as e:
        print("[Stars] public board:", e)
        return False


def fetch_public():
    """Public rooms announced in the last couple of minutes, from anywhere in the world."""
    req = urllib.request.Request(DIRECTORY + "/json?poll=1&since=%ds" % (PUB_WINDOW + 30),
                                 headers={"User-Agent": "StarsMultiplayer"})
    data = urllib.request.urlopen(req, timeout=6).read().decode(errors="ignore")
    now = time.time()
    found = {}
    for line in data.splitlines():
        try:
            ev = json.loads(line)
            if ev.get("event") != "message" or now - float(ev.get("time", 0)) > PUB_WINDOW:
                continue
            d = json.loads(ev["message"])
            short = str(d.get("short", ""))[:8]
            if d.get("closed"):
                found.pop(short, None)
                continue
            ip, port = str(d["ip"]), int(d["port"])
            if re.fullmatch(r"[0-9.]+", ip):
                if len(ip.split(".")) != 4 or not all(x.isdigit() and int(x) < 256 for x in ip.split(".")):
                    continue
            elif not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9.\-]{0,62}", ip):
                continue
            if not 1024 <= port <= 65535:
                continue
            found[short] = {"room": str(d.get("room", ""))[:40], "short": short,
                            "players": int(d.get("players", 1)), "ip": ip, "port": port}
        except Exception:
            continue
    return list(found.values())


def prefs_file():
    return os.path.join(bpy.utils.user_resource('CONFIG', create=True), "stars_prefs.json")


_loading_prefs = [False]


def save_prefs(wm):
    try:
        with open(prefs_file(), "w") as f:
            json.dump({"name": wm.stars_name, "color": list(wm.stars_color)}, f)
    except Exception as e:
        print("[Stars] couldn't save name/color:", e)


def load_prefs(wm):
    try:
        with open(prefs_file()) as f:
            d = json.load(f)
    except Exception:
        return
    _loading_prefs[0] = True
    try:
        if d.get("name"):
            wm.stars_name = str(d["name"])[:32]
        c = d.get("color")
        if isinstance(c, list) and len(c) == 3:
            wm.stars_color = [min(1.0, max(0.0, float(x))) for x in c]
    except Exception as e:
        print("[Stars] couldn't load name/color:", e)
    finally:
        _loading_prefs[0] = False


def _load_prefs_timer():
    try:
        load_prefs(bpy.context.window_manager)
    except Exception:
        return 0.5   # Blender isn't ready yet: try again
    return None


def push_profile(wm):
    """Tell the room your new name / color."""
    net = S["net"]
    if not (S["active"] and net):
        return
    name, color = (wm.stars_name or "Player")[:32], list(wm.stars_color)
    if net.is_host:
        h = net.hellos.get(S["me"])
        if h is not None:
            h["name"], h["color"] = name, color
    net.send({"t": "prof", "id": S["me"], "name": name, "color": color})


def avatar_file():
    return os.path.join(bpy.utils.user_resource('CONFIG', create=True), "stars_avatar.json")


def save_avatar():
    try:
        with open(avatar_file(), "w") as f:
            json.dump(AVATAR["av"], f)
    except Exception as e:
        print("[Stars] couldn't save picture:", e)


def load_avatar():
    try:
        with open(avatar_file()) as f:
            AVATAR["av"] = clean_av(json.load(f))
    except Exception:
        pass


def set_avatar(av):
    """Use this picture from now on and tell the room."""
    AVATAR["av"] = av
    save_avatar()
    net = S["net"]
    if S["active"] and net:
        if net.is_host:
            h = net.hellos.get(S["me"])
            if h is not None:
                if av:
                    h["av"] = av
                else:
                    h.pop("av", None)
        net.send({"t": "av", "id": S["me"], "av": av})


# ----------------------------------------------------------------------------
# Session state
# ----------------------------------------------------------------------------

def fresh_state():
    return {
        "active": False,
        "me": "",
        "peers": {},       # id -> {name,color,v,f,c,s}
        "cache": {},       # object name -> rounded transform
        "pc": {},          # object name -> last property dump
        "lc": {},          # "obj|mod" / "obj|con" -> signature
        "mhash": {},       # object name -> mesh signature
        "mtc": {},         # object name -> material slot names
        "matsig": {},      # material name -> signature
        "collsig": None,
        "collnames": set(),
        "scsig": None,
        "dirty": set(),
        "pending": {},
        "room": "",
        "code": "",
        "status": "",
        "addr": "",
        "port": DEFAULT_PORT,
        "short": "",
        "public": False,
        "last_pres": None,
        "last_pres_t": 0.0,
        "last_mesh_t": 0.0,
        "t_props": 0.0,
        "t_slow": 0.0,
        "rs": dict(ROOM_DEFAULTS),   # room settings (host decides)
        "acts": {},          # action id -> {"a": author id, "undone": bool}   (everyone's, metadata only)
        "order": [],         # action ids, oldest -> newest
        "redo_order": [],    # undone action ids, oldest -> newest
        "hist": {},          # MY actions only: action id -> list of changes (old/new data)
        "open": [], "open_idx": {}, "open_t": 0.0,
        "last_commit_id": None, "last_commit_t": 0.0, "quiet": False,
        "mpay": {},          # object name -> last mesh payload (needed to undo mesh edits)
        "kind": {},          # object name -> [type, light type] (needed to restore deleted objects)
        "lv": {},            # "obj|mod" / "obj|con" -> full list (the signature lives in "lc")
        "matv": {},          # material name -> last dump
        "collv": None,       # last collections dump
        "relay_status": "", "lan": None, "relay_t": 0.0,   # Easy connect
        "mouse_down": False, "boundary": 0.0, "open_start": 0.0, "watch_t": 0.0,   # undo step boundaries
        "quiet_until": 0.0,  # right after an undo, nothing is logged for a moment (no phantom steps)
        "need_resync": False, "last_resync": 0.0,   # view-only guests: ask the host to put things back
    }


S = fresh_state()
S["net"] = None
S["ips"] = []


def sig(d):
    return hash(json.dumps(d, separators=(",", ":"), sort_keys=True))


def r5(v):
    return tuple(round(x, 5) for x in v)


def read_x(ob):
    return (r5(ob.location), r5(ob.rotation_euler), r5(ob.scale))


def xl(t):
    return [list(t[0]), list(t[1]), list(t[2])]


def note_list(name, kind, lst):
    key = name + "|" + kind
    S["lc"][key] = sig(lst)
    S["lv"][key] = lst


def note_mat(name, d):
    S["matsig"][name] = sig(d)
    S["matv"][name] = d


def note_coll(cd):
    S["collsig"] = sig(cd)
    S["collnames"] = set(cd) - {"__root__"}
    S["collv"] = cd


def coll_adjust(add=None, remove=None):
    """Remote changes add/remove objects too. Mirror that in the remembered collections, otherwise
    the next poll thinks YOU changed the collections and records a fake undo step."""
    cv = S["collv"]
    if cv is None or "__root__" not in cv:
        return
    nd = {k: {"o": list(v["o"]), "c": list(v["c"])} for k, v in cv.items()}
    if add and add not in nd["__root__"]["o"]:
        nd["__root__"]["o"].append(add)
    if remove:
        for v in nd.values():
            if remove in v["o"]:
                v["o"].remove(remove)
    note_coll(nd)


def note_mesh(ob):
    p = mesh_payload(ob)
    S["mhash"][ob.name] = sig(p)
    S["mpay"][ob.name] = p


def entry_from_cache(n):
    """Rebuild an object's last known state from the caches (used when it gets deleted)."""
    kind = S["kind"].get(n)
    x = S["cache"].get(n)
    if not kind or x is None:
        return None
    d = None
    if kind[0] == 'MESH':
        d = S["mpay"].get(n)
    elif kind[0] == 'LIGHT':
        d = {"lt": kind[1] or "POINT"}
    return {"n": n, "k": kind[0], "d": d, "x": xl(x), "pr": S["pc"].get(n) or {},
            "mod": S["lv"].get(n + "|mod") or [], "con": S["lv"].get(n + "|con") or []}


def redraw():
    try:
        for win in bpy.context.window_manager.windows:
            for area in win.screen.areas:
                if area.type == 'VIEW_3D':
                    area.tag_redraw()
    except Exception:
        pass


def rebuild_ui():
    wm = bpy.context.window_manager
    wm.stars_peers.clear()
    for pid, p in S["peers"].items():
        it = wm.stars_peers.add()
        it.name = p["name"]
        it.color = p["color"]
        it.pid = pid
    for win in wm.windows:
        for area in win.screen.areas:
            area.tag_redraw()


# ----------------------------------------------------------------------------
# Generic property sync (any Blender RNA struct -> JSON and back)
# ----------------------------------------------------------------------------

SKIP_PROPS = {
    "rna_type", "name", "name_full", "original", "id_data", "users", "session_uid",
    "is_evaluated", "bound_box", "mode", "data", "active_material", "location",
    "rotation_euler", "scale", "dimensions", "matrix_basis", "matrix_local",
    "matrix_world", "select", "show_expanded", "is_active", "tag", "use_fake_user",
    "frame_current_final", "is_runtime_data", "library", "preview", "asset_data",
}


def _refs():
    return {"Object": bpy.data.objects, "Material": bpy.data.materials,
            "Collection": bpy.data.collections, "World": bpy.data.worlds,
            "Image": bpy.data.images}


def jv(v):
    if v is None or isinstance(v, (bool, int, float, str)):
        return v
    return [jv(x) for x in v]  # raises TypeError for things we can't send


def rna_dump(obj):
    d = {}
    refs = _refs()
    for p in obj.bl_rna.properties:
        pid = p.identifier
        if pid in SKIP_PROPS or p.is_readonly or p.type == 'COLLECTION':
            continue
        try:
            if p.type == 'POINTER':
                if p.fixed_type.identifier in refs:
                    v = getattr(obj, pid)
                    d[pid] = {"r": v.name} if v is not None else None
            else:
                v = getattr(obj, pid)
                if p.type == 'ENUM' and p.is_enum_flag:
                    v = sorted(v)
                d[pid] = jv(v)
        except Exception:
            pass
    return d


def rna_apply(obj, d):
    refs = _refs()
    for pid, v in d.items():
        p = obj.bl_rna.properties.get(pid)
        if p is None or p.is_readonly:
            continue
        try:
            if p.type == 'POINTER':
                coll = refs.get(p.fixed_type.identifier)
                if coll is None:
                    continue
                setattr(obj, pid, coll.get(v["r"]) if v else None)
            elif p.type == 'ENUM' and p.is_enum_flag:
                setattr(obj, pid, set(v))
            else:
                setattr(obj, pid, v)
        except Exception:
            pass


SYNC_TYPES = ('MESH', 'EMPTY', 'LIGHT', 'CAMERA')


def full_props(ob):
    d = rna_dump(ob)
    if ob.type in ('LIGHT', 'CAMERA') and ob.data:
        d.update({"data." + k: v for k, v in rna_dump(ob.data).items()})
    return d


def apply_props(ob, d):
    od, dd = {}, {}
    for k, v in d.items():
        if k.startswith("data."):
            dd[k[5:]] = v
        else:
            od[k] = v
    rna_apply(ob, od)
    if dd and ob.data:
        rna_apply(ob.data, dd)


# --- modifiers / constraints -------------------------------------------------

def lists_dump(ob, kind):
    coll = ob.modifiers if kind == "mod" else ob.constraints
    return [{"n": m.name, "ty": m.type, "p": rna_dump(m)} for m in coll]


def apply_list(ob, kind, lst):
    coll = ob.modifiers if kind == "mod" else ob.constraints
    want = {(e["n"], e["ty"]) for e in lst}
    for m in list(coll):
        if (m.name, m.type) not in want:
            try:
                coll.remove(m)
            except Exception:
                pass
    for i, e in enumerate(lst):
        m = coll.get(e["n"])
        if m is None or m.type != e["ty"]:
            try:
                if kind == "mod":
                    m = coll.new(e["n"], e["ty"])
                else:
                    m = coll.new(e["ty"])
                    m.name = e["n"]
            except Exception:
                continue
        rna_apply(m, e["p"])
        try:
            cur = list(coll).index(m)
            if cur != i:
                coll.move(cur, i)
        except Exception:
            pass


# --- materials ---------------------------------------------------------------

def mat_dump(m):
    d = {"p": rna_dump(m), "nodes": None, "links": []}
    if getattr(m, "use_nodes", False) and m.node_tree:
        nt = m.node_tree
        nodes = []
        for n in nt.nodes:
            ins = {}
            for i, s in enumerate(n.inputs):
                if hasattr(s, "default_value"):
                    try:
                        ins[str(i)] = jv(s.default_value)
                    except Exception:
                        pass
            nodes.append({"n": n.name, "t": n.bl_idname, "loc": list(n.location),
                          "p": rna_dump(n), "i": ins})
        links = []
        for l in nt.links:
            try:
                links.append([l.from_node.name, list(l.from_node.outputs).index(l.from_socket),
                              l.to_node.name, list(l.to_node.inputs).index(l.to_socket)])
            except Exception:
                pass
        d["nodes"] = nodes
        d["links"] = links
    return d


def mat_apply(name, d):
    m = bpy.data.materials.get(name) or bpy.data.materials.new(name)
    rna_apply(m, d["p"])
    if d["nodes"] is not None:
        try:
            m.use_nodes = True
            nt = m.node_tree
            want = {n["n"] for n in d["nodes"]}
            for n in list(nt.nodes):
                if n.name not in want:
                    nt.nodes.remove(n)
            for e in d["nodes"]:
                n = nt.nodes.get(e["n"])
                if n is None or n.bl_idname != e["t"]:
                    if n:
                        nt.nodes.remove(n)
                    n = nt.nodes.new(e["t"])
                    n.name = e["n"]
                n.location = e["loc"]
                rna_apply(n, e["p"])
                for i, v in e["i"].items():
                    try:
                        n.inputs[int(i)].default_value = v
                    except Exception:
                        pass
            nt.links.clear()
            for fn, fi, tn, ti in d["links"]:
                try:
                    nt.links.new(nt.nodes[fn].outputs[fi], nt.nodes[tn].inputs[ti])
                except Exception:
                    pass
        except Exception as ex:
            print("[Stars] material apply:", ex)
    note_mat(name, mat_dump(m))


# --- collections & scene -----------------------------------------------------

def coll_dump():
    root = bpy.context.scene.collection
    d = {"__root__": {"o": [o.name for o in root.objects],
                      "c": [c.name for c in root.children]}}
    for c in bpy.data.collections:
        d[c.name] = {"o": [o.name for o in c.objects], "c": [x.name for x in c.children]}
    return d


def coll_apply(d):
    root = bpy.context.scene.collection
    for n in d:
        if n != "__root__" and n not in bpy.data.collections:
            bpy.data.collections.new(n)
    known = {o for e in d.values() for o in e["o"]}
    for n, e in d.items():
        c = root if n == "__root__" else bpy.data.collections.get(n)
        if c is None:
            continue
        for on in e["o"]:
            ob = bpy.data.objects.get(on)
            if ob and ob.name not in c.objects:
                c.objects.link(ob)
        for ob in list(c.objects):
            if ob.name not in e["o"] and ob.name in known:
                c.objects.unlink(ob)
        for cn in e["c"]:
            ch = bpy.data.collections.get(cn)
            if ch and ch is not c and ch.name not in c.children:
                try:
                    c.children.link(ch)
                except Exception:
                    pass
        for ch in list(c.children):
            if ch.name not in e["c"] and ch.name in d:
                try:
                    c.children.unlink(ch)
                except Exception:
                    pass
    for c in list(bpy.data.collections):
        if c.name not in d and c.name in S["collnames"]:
            bpy.data.collections.remove(c)
    cd = coll_dump()
    note_coll(cd)


def scene_dump():
    sc = bpy.context.scene
    d = {"sc": rna_dump(sc), "rd": rna_dump(sc.render)}
    if sc.world:
        d["wd"] = rna_dump(sc.world)
        d["wn"] = sc.world.name
    return d


def scene_apply(d):
    sc = bpy.context.scene
    rna_apply(sc, d["sc"])
    rna_apply(sc.render, d["rd"])
    if "wd" in d:
        w = bpy.data.worlds.get(d["wn"]) or bpy.data.worlds.new(d["wn"])
        sc.world = w
        rna_apply(w, d["wd"])
    S["scsig"] = sig(scene_dump())


# ----------------------------------------------------------------------------
# Meshes and objects
# ----------------------------------------------------------------------------

def mesh_payload(ob):
    me = ob.data
    mt = [m.name if m else "" for m in me.materials]
    if ob.mode == 'EDIT':
        bm = bmesh.from_edit_mesh(me)
        bm.verts.index_update()
        verts = [[round(c, 4) for c in v.co] for v in bm.verts]
        faces = [[v.index for v in f.verts] for f in bm.faces]
        edges = [[v.index for v in e.verts] for e in bm.edges if not e.link_faces]
        sm = [bool(f.smooth) for f in bm.faces]
        mi = [f.material_index for f in bm.faces]
        uvs = {}
        for name, layer in bm.loops.layers.uv.items():
            uvs[name] = [round(x, 4) for f in bm.faces for l in f.loops for x in l[layer].uv]
    else:
        verts = [[round(c, 4) for c in v.co] for v in me.vertices]
        faces = [list(p.vertices) for p in me.polygons]
        edges = [list(e.vertices) for e in me.edges if e.is_loose]
        sm = [bool(p.use_smooth) for p in me.polygons]
        mi = [p.material_index for p in me.polygons]
        uvs = {}
        nl = len(me.loops)
        for uvl in me.uv_layers:
            buf = [0.0] * (nl * 2)
            uvl.data.foreach_get("uv", buf)
            uvs[uvl.name] = [round(x, 4) for x in buf]
    return {"v": verts, "f": faces, "e": edges, "sm": sm, "mi": mi, "uv": uvs, "mt": mt}


def modal_running():
    # True while a modal tool (loop cut, knife, grab, sculpt stroke...) is running
    try:
        for w in bpy.context.window_manager.windows:
            for op in w.modal_operators:
                idn = op.bl_idname.lower()
                if not ("stars" in idn and "watch" in idn):
                    return True
    except Exception:
        pass
    return False


def watch_running():
    try:
        for w in bpy.context.window_manager.windows:
            for op in w.modal_operators:
                idn = op.bl_idname.lower()
                if "stars" in idn and "watch" in idn:
                    return True
    except Exception:
        pass
    return False


def ensure_watch():
    """Start the little input watcher that tells us when a mouse click / key press ends,
    so every drag, click and key action becomes exactly one Ctrl+Z step (like normal Blender)."""
    now = time.time()
    if now - S["watch_t"] < 1.0 or watch_running():
        return
    S["watch_t"] = now
    wm = bpy.context.window_manager
    for win in wm.windows:
        for area in win.screen.areas:
            if area.type != 'VIEW_3D':
                continue
            for region in area.regions:
                if region.type == 'WINDOW':
                    with bpy.context.temp_override(window=win, area=area, region=region):
                        bpy.ops.stars.watch('INVOKE_DEFAULT')
                    return


def apply_materials(me, d):
    me.materials.clear()
    for n in d.get("mt", []):
        if not n:
            me.materials.append(None)
            continue
        m = bpy.data.materials.get(n)
        if m is None:
            m = bpy.data.materials.new(n)
            note_mat(n, mat_dump(m))
        me.materials.append(m)


def set_mesh_edit(ob, d):
    # Rebuild the mesh live while the local user is in Edit Mode.
    me = ob.data
    bm = bmesh.from_edit_mesh(me)
    bm.clear()
    verts = [bm.verts.new(c) for c in d["v"]]
    for e in d["e"]:
        try:
            bm.edges.new((verts[e[0]], verts[e[1]]))
        except (ValueError, IndexError):
            pass
    faces = []
    for f in d["f"]:
        try:
            faces.append(bm.faces.new([verts[i] for i in f]))
        except (ValueError, IndexError):
            faces.append(None)
    sm, mi = d.get("sm", []), d.get("mi", [])
    for i, fc in enumerate(faces):
        if fc is None:
            continue
        if i < len(sm):
            fc.smooth = sm[i]
        if i < len(mi):
            fc.material_index = mi[i]
    for name, flat in d.get("uv", {}).items():
        layer = bm.loops.layers.uv.get(name) or bm.loops.layers.uv.new(name)
        off = 0
        for i, f in enumerate(d["f"]):
            fc = faces[i]
            if fc is not None:
                for j, l in enumerate(fc.loops):
                    k = (off + j) * 2
                    if k + 1 < len(flat):
                        l[layer].uv = (flat[k], flat[k + 1])
            off += len(f)
    apply_materials(me, d)
    bm.normal_update()
    bmesh.update_edit_mesh(me)
    note_mesh(ob)
    S["mtc"][ob.name] = [m.name if m else "" for m in me.materials]


def set_mesh(ob, d):
    if ob.mode in ('EDIT', 'SCULPT') and modal_running():
        S["pending"][ob.name] = d  # a tool is mid-action: apply right after
        return
    if ob.mode == 'EDIT':
        set_mesh_edit(ob, d)
        return
    me = ob.data
    me.clear_geometry()
    me.from_pydata(d["v"], d["e"], d["f"])
    me.update()
    apply_materials(me, d)
    npoly = len(me.polygons)
    if len(d.get("sm", [])) == npoly:
        me.polygons.foreach_set("use_smooth", d["sm"])
    if len(d.get("mi", [])) == npoly:
        me.polygons.foreach_set("material_index", d["mi"])
    nl = len(me.loops)
    for name, flat in d.get("uv", {}).items():
        if len(flat) == nl * 2:
            uvl = me.uv_layers.new(name=name)
            uvl.data.foreach_set("uv", flat)
    me.update()
    note_mesh(ob)
    S["mtc"][ob.name] = [m.name if m else "" for m in me.materials]


def obj_entry(ob):
    if ob.type not in SYNC_TYPES:
        return None
    d = None
    if ob.type == 'MESH':
        d = mesh_payload(ob)
    elif ob.type == 'LIGHT':
        d = {"lt": ob.data.type}
    return {"n": ob.name, "k": ob.type, "d": d,
            "x": [list(ob.location), list(ob.rotation_euler), list(ob.scale)],
            "pr": full_props(ob), "mod": lists_dump(ob, "mod"), "con": lists_dump(ob, "con")}


def upsert(e, force=False):
    """Create the object if missing (mesh + transform only)."""
    name, kind, d = e["n"], e["k"], e["d"]
    ob = bpy.data.objects.get(name)
    if ob is None:
        data = None
        if kind == 'MESH':
            data = bpy.data.meshes.new(name)
        elif kind == 'LIGHT':
            data = bpy.data.lights.new(name, d.get("lt", "POINT"))
        elif kind == 'CAMERA':
            data = bpy.data.cameras.new(name)
        ob = bpy.data.objects.new(name, data)
        bpy.context.scene.collection.objects.link(ob)
        coll_adjust(add=ob.name)
        if kind == 'MESH' and d:
            set_mesh(ob, d)
    elif kind == 'MESH' and d and ob.type == 'MESH' and (force or ob.mode != 'EDIT'):
        if mesh_payload(ob) != d:
            set_mesh(ob, d)
    S["kind"][ob.name] = [kind, (d or {}).get("lt")]
    loc, rot, scl = e["x"]
    ob.location, ob.rotation_euler, ob.scale = loc, rot, scl
    S["cache"][ob.name] = read_x(ob)


def extras(e):
    """Second pass: properties, modifiers, constraints (parents may exist now)."""
    ob = bpy.data.objects.get(e["n"])
    if not ob:
        return
    apply_props(ob, e.get("pr") or {})
    for k in ("mod", "con"):
        if e.get(k) is not None:
            apply_list(ob, k, e[k])
            note_list(ob.name, k, lists_dump(ob, k))
    S["pc"][ob.name] = full_props(ob)


def forget(name):
    for k in ("cache", "mhash", "pending", "pc", "mtc", "mpay", "kind"):
        S[k].pop(name, None)
    S["lc"].pop(name + "|mod", None)
    S["lc"].pop(name + "|con", None)
    S["lv"].pop(name + "|mod", None)
    S["lv"].pop(name + "|con", None)


def remove_obj(name):
    ob = bpy.data.objects.get(name)
    if ob:
        bpy.data.objects.remove(ob, do_unlink=True)
    coll_adjust(remove=name)
    forget(name)
    redraw()


def apply_x(entries):
    changed = False
    for name, loc, rot, scl in entries:
        ob = bpy.data.objects.get(name)
        if not ob:
            continue
        ob.location = loc
        ob.rotation_euler = rot
        ob.scale = scl
        S["cache"][name] = read_x(ob)  # read back so rounding can't ping-pong
        changed = True
    if changed:
        redraw()


def full_state(lock=False):
    return {"t": "full", "lock": lock,
            "o": [e for e in (obj_entry(o) for o in bpy.data.objects) if e],
            "mats": {m.name: mat_dump(m) for m in bpy.data.materials},
            "col": coll_dump(), "sc": scene_dump()}


def apply_objects(ents, force=False):
    for e in ents:
        upsert(e, force)
    for e in ents:
        extras(e)


def seed_caches():
    S["cache"] = {o.name: read_x(o) for o in bpy.data.objects}
    S["pc"] = {o.name: full_props(o) for o in bpy.data.objects}
    S["lc"], S["lv"] = {}, {}
    for o in bpy.data.objects:
        for k in ("mod", "con"):
            note_list(o.name, k, lists_dump(o, k))
    S["matsig"], S["matv"] = {}, {}
    for m in bpy.data.materials:
        note_mat(m.name, mat_dump(m))
    cd = coll_dump()
    note_coll(cd)
    S["scsig"] = sig(scene_dump())
    S["mtc"] = {o.name: [m.name if m else "" for m in o.data.materials]
                for o in bpy.data.objects if o.type == 'MESH'}
    S["mhash"] = {}
    S["mpay"] = {o.name: mesh_payload(o) for o in bpy.data.objects if o.type == 'MESH'}
    S["kind"] = {o.name: [o.type, o.data.type if o.type == 'LIGHT' else None]
                 for o in bpy.data.objects if o.type in SYNC_TYPES}
    S["dirty"] = set()
    S["pending"] = {}


def view_info():
    try:
        for win in bpy.context.window_manager.windows:
            for area in win.screen.areas:
                if area.type == 'VIEW_3D':
                    r3d = area.spaces.active.region_3d
                    eye = r3d.view_matrix.inverted().translation
                    return [round(x, 3) for x in eye], [round(x, 3) for x in r3d.view_location]
    except Exception:
        pass
    return None, None


def on_depsgraph(scene, depsgraph):
    if not S["active"]:
        return
    for u in depsgraph.updates:
        if not u.is_updated_geometry:
            continue
        if isinstance(u.id, bpy.types.Object):
            S["dirty"].add(u.id.name)
        elif isinstance(u.id, bpy.types.Mesh):
            for ob in bpy.data.objects:
                if ob.type == 'MESH' and ob.data and ob.data.name == u.id.name:
                    S["dirty"].add(ob.name)


# ----------------------------------------------------------------------------
# Incoming messages and the sync loop
# ----------------------------------------------------------------------------

def handle(msg):
    net = S["net"]
    if net is None:
        return
    t = msg.get("t")
    if t == "hello":
        if msg["id"] == S["me"]:
            return
        S["peers"][msg["id"]] = {"name": msg["name"], "color": msg["color"],
                                 "v": None, "f": None, "c": None, "s": [],
                                 "dv": None, "df": None, "dc": None,
                                 "av": clean_av(msg.get("av")), "tex": None}
        if msg.get("host"):
            S["room"] = msg.get("room", "")
        rebuild_ui()
        S["last_pres"] = None
        if net.is_host:
            net.send_to_id(msg["id"], {"t": "rs", "d": dict(S["rs"])})  # room settings first
            net.send_to_id(msg["id"], full_state(lock=not S["rs"].get("edit", True)))  # host scene is the truth
    elif t == "resync":
        if net.is_host and msg.get("id") in S["peers"]:  # a view-only guest changed something: put it back
            net.send_to_id(msg["id"], full_state(lock=not S["rs"].get("edit", True)))
    elif t == "prof":
        p = S["peers"].get(msg["id"])
        if p:
            p["name"] = str(msg.get("name") or "Player")[:32]
            c = msg.get("color")
            if isinstance(c, (list, tuple)) and len(c) == 3:
                p["color"] = [float(x) for x in c]
            rebuild_ui()
            redraw()
    elif t == "av":
        p = S["peers"].get(msg["id"])
        if p:
            p["av"] = clean_av(msg.get("av"))
            p["tex"] = None
            redraw()
    elif t == "full":
        for n, d in msg.get("mats", {}).items():
            mat_apply(n, d)
        apply_objects(msg["o"], bool(msg.get("lock")))
        if "col" in msg:
            coll_apply(msg["col"])
        if "sc" in msg and bpy.context.window_manager.stars_sync_scene:
            scene_apply(msg["sc"])
        redraw()
    elif t == "add":
        apply_objects(msg["o"])
        redraw()
    elif t == "x":
        apply_x(msg["o"])
    elif t == "m":
        ob = bpy.data.objects.get(msg["n"])
        if ob and ob.type == 'MESH':
            set_mesh(ob, msg["d"])
            redraw()
    elif t == "del":
        for n in msg["n"]:
            remove_obj(n)
    elif t == "pr":
        ob = bpy.data.objects.get(msg["n"])
        if ob:
            apply_props(ob, msg["d"])
            new = full_props(ob)
            cache = S["pc"].setdefault(ob.name, {})
            for k in msg["d"]:
                if k in new:
                    cache[k] = new[k]
            redraw()
    elif t == "md":
        ob = bpy.data.objects.get(msg["n"])
        if ob:
            apply_list(ob, msg["k"], msg["l"])
            note_list(ob.name, msg["k"], lists_dump(ob, msg["k"]))
            redraw()
    elif t == "mat":
        if bpy.context.window_manager.stars_sync_materials:
            mat_apply(msg["n"], msg["d"])
    elif t == "col":
        coll_apply(msg["d"])
        redraw()
    elif t == "sc":
        if bpy.context.window_manager.stars_sync_scene:
            scene_apply(msg["d"])
            redraw()
    elif t == "p":
        p = S["peers"].get(msg["id"])
        if p:
            p["v"], p["f"], p["c"], p["s"] = msg["v"], msg["f"], msg["c"], msg["s"]
            redraw()
    elif t == "bye":
        S["peers"].pop(msg["id"], None)
        purge_author(msg["id"])
        rebuild_ui()
        redraw()
    elif t == "deny":
        end_session(msg.get("why", "Couldn't join the room"))
    elif t == "rs":
        S["rs"].update(msg.get("d", {}))  # only the host's "rs" is ever relayed to us
        rebuild_ui()
    elif t == "act":
        register_act(msg["id"], msg["a"])
    elif t == "ud":
        set_undone(msg["id"], bool(msg["u"]))
    elif t == "req":
        if msg.get("to") == S["me"] and not is_locked():
            a = S["acts"].get(msg["id"])
            want_undo = msg.get("do") == "undo"
            if a and a["undone"] != want_undo:
                run_action(msg["id"], want_undo)
    elif t == "kick":
        end_session("You were kicked by the host")
    elif t in ("_closed", "_err"):
        if not net.is_host:
            end_session("Disconnected from room")


def sync_objects(net):
    names = set(bpy.data.objects.keys())
    known = set(S["cache"])
    added = []
    for n in names - known:
        ob = bpy.data.objects[n]
        S["cache"][n] = read_x(ob)
        e = obj_entry(ob)
        if e:
            if e["k"] == 'MESH':
                S["mhash"][n] = sig(e["d"])
                S["mtc"][n] = e["d"]["mt"]
            S["pc"][n] = e["pr"]
            note_list(n, "mod", e["mod"])
            note_list(n, "con", e["con"])
            S["kind"][n] = [ob.type, ob.data.type if ob.type == 'LIGHT' else None]
            if e["k"] == 'MESH':
                S["mpay"][n] = e["d"]
            added.append(e)
    if added:
        for e in added:
            log_change("add", ("add", e["n"]), None, e)
        net.send({"t": "add", "o": added})
    gone = list(known - names)
    for n in gone:
        ent = entry_from_cache(n)
        if ent:
            log_change("del", ("del", n), ent, None)
        forget(n)
    if gone:
        net.send({"t": "del", "n": gone})


def sync_meshes(net):
    sent_now = set()
    tnow = time.time()
    if S["dirty"] and tnow - S["last_mesh_t"] > 0.1:
        dirty, S["dirty"] = S["dirty"], set()
        S["last_mesh_t"] = tnow
        for n in dirty:
            ob = bpy.data.objects.get(n)
            if not ob or ob.type != 'MESH' or n not in S["cache"]:
                continue
            d = mesh_payload(ob)
            s = sig(d)
            if S["mhash"].get(n) != s:
                old = S["mpay"].get(n)
                S["mhash"][n] = s
                S["mpay"][n] = d
                if old is not None and old != d:
                    log_change("m", ("m", n), old, d)
                sent_now.add(n)
                net.send({"t": "m", "id": S["me"], "n": n, "d": d})
    for n in list(S["pending"]):
        ob = bpy.data.objects.get(n)
        if n in sent_now or not ob:
            S["pending"].pop(n, None)
        elif ob.mode not in ('EDIT', 'SCULPT') or not modal_running():
            set_mesh(ob, S["pending"].pop(n))
            redraw()


def sync_transforms(net):
    out = []
    for ob in bpy.data.objects:
        cur = read_x(ob)
        old = S["cache"].get(ob.name)
        if old != cur:
            if old is not None:
                log_change("x", ("x", ob.name), xl(old), xl(cur))
            S["cache"][ob.name] = cur
            out.append([ob.name, list(ob.location), list(ob.rotation_euler), list(ob.scale)])
    if out:
        net.send({"t": "x", "id": S["me"], "o": out})


def poll_props(net):
    for ob in bpy.data.objects:
        n = ob.name
        if n not in S["cache"]:
            continue
        d = full_props(ob)
        old = S["pc"].get(n)
        if old is None:
            S["pc"][n] = d
        else:
            ch = {k: v for k, v in d.items() if old.get(k) != v}
            if ch:
                log_change("pr", ("pr", n), {k: old.get(k) for k in ch}, dict(ch))
                S["pc"][n] = d
                net.send({"t": "pr", "n": n, "d": ch})
        for kind in ("mod", "con"):
            l = lists_dump(ob, kind)
            s = sig(l)
            key = n + "|" + kind
            if S["lc"].get(key) is None:
                note_list(n, kind, l)
            elif S["lc"][key] != s:
                log_change("md", ("md", n, kind), S["lv"].get(key), l)
                note_list(n, kind, l)
                net.send({"t": "md", "n": n, "k": kind, "l": l})
        if ob.type == 'MESH' and ob.mode in ('EDIT', 'SCULPT'):
            S["dirty"].add(n)
        if ob.type == 'MESH':
            mt = [m.name if m else "" for m in ob.data.materials]
            oldmt = S["mtc"].get(n)
            S["mtc"][n] = mt
            if oldmt is not None and oldmt != mt:
                S["dirty"].add(n)


def poll_slow(net):
    wm = bpy.context.window_manager
    for m in (list(bpy.data.materials) if wm.stars_sync_materials else []):
        d = mat_dump(m)
        s = sig(d)
        if S["matsig"].get(m.name) != s:
            old = S["matv"].get(m.name)
            if old is not None:
                log_change("mat", ("mat", m.name), old, d, slow=True)
            note_mat(m.name, d)
            net.send({"t": "mat", "n": m.name, "d": d})
    cd = coll_dump()
    s = sig(cd)
    if S["collsig"] != s:
        if S["collv"] is not None:
            log_change("col", ("col",), S["collv"], cd, slow=True)
        note_coll(cd)
        net.send({"t": "col", "d": cd})
    if not wm.stars_sync_scene:
        return
    sd = scene_dump()
    s = sig(sd)
    if S["scsig"] != s:
        S["scsig"] = s
        net.send({"t": "sc", "d": sd})


def send_presence(net, now):
    if now - S["last_pres_t"] <= 0.04:
        return
    S["last_pres_t"] = now
    eye, focus = view_info()
    if not eye:
        return
    cur = [round(x, 3) for x in bpy.context.scene.cursor.location]
    sel = [o.name for o in bpy.context.selected_objects][:20]
    pres = ["p", eye, focus, cur, sel]
    if pres != S["last_pres"]:
        S["last_pres"] = pres
        net.send({"t": "p", "id": S["me"], "v": eye, "f": focus, "c": cur, "s": sel})


class _Sink:
    """Stands in for the network while you are view-only: it just notes that something changed."""
    def send(self, msg, skip=None):
        S["need_resync"] = True


def is_locked():
    """True for a guest in a room where the host turned editing off."""
    net = S["net"]
    return bool(S["active"] and net and not net.is_host and not S["rs"].get("edit", True))


def drop_local_objects():
    # a view-only guest can't add objects: anything new that didn't come from the host goes away
    for n in [n for n in bpy.data.objects.keys() if n not in S["cache"]]:
        ob = bpy.data.objects.get(n)
        if ob and ob.type in SYNC_TYPES:
            remove_obj(n)


def safe(fn, *a):
    try:
        fn(*a)
    except Exception as e:  # one broken sync must not stop the others
        print("[Stars] %s error: %s" % (fn.__name__, e))


def tick():
    try:
        if SCAN["done"]:
            SCAN["done"] = False
            redraw()
        if S["active"] and S["net"]:
            net = S["net"]
            if net.is_host:
                net.info["players"] = len(S["peers"]) + 1
                rl = net.relay
                if rl is not None and not rl.alive and time.time() - S["relay_t"] > 10:
                    S["relay_t"] = time.time()
                    net.relay = None
                    S["relay_status"] = "Easy connect dropped - reconnecting..."
                    start_relay(net, rl.server, rl.local_port)
            while True:
                try:
                    msg = net.q.get_nowait()
                except queue.Empty:
                    break
                safe(handle, msg)
                if not S["active"]:
                    break
            if not S["active"]:
                return 0.05
            now = time.time()
            safe(ensure_watch)
            locked = is_locked()
            out = net
            if locked:
                out = _Sink()          # nothing a view-only guest does is sent or put in undo history
                S["quiet"] = True
                safe(drop_local_objects)
            try:
                safe(sync_objects, out)
                safe(sync_meshes, out)
                safe(sync_transforms, out)
                if now - S["t_props"] > 0.2:
                    S["t_props"] = now
                    safe(poll_props, out)
                if now - S["t_slow"] > 0.5:
                    S["t_slow"] = now
                    safe(poll_slow, out)
            finally:
                if locked:
                    S["quiet"] = False
            safe(send_presence, net, now)
            if locked:
                if S["need_resync"] and now - S["last_resync"] > 1.0:
                    S["need_resync"] = False
                    S["last_resync"] = now
                    net.send({"t": "resync", "id": S["me"]})  # host sends the real scene back
            else:
                safe(commit_open, net)
    except Exception as e:
        print("[Stars] tick error:", e)
    return 0.05


# ----------------------------------------------------------------------------
# Smooth cursors
# Presence arrives ~20x a second. Drawing it raw looks steppy, so every other
# player's cursor eases toward its newest position at your screen's frame rate.
# ----------------------------------------------------------------------------

def shown(p, k):
    return p.get("d" + k) or p.get(k)


_smooth_t = [time.time()]


def smooth_tick():
    try:
        now = time.time()
        dt = min(now - _smooth_t[0], 0.25)
        _smooth_t[0] = now
        if S["active"] and S["peers"]:
            a = 1.0 - math.exp(-dt / SMOOTH_TAU)
            moving = False
            for p in S["peers"].values():
                for tk in ("v", "f", "c"):
                    dk = "d" + tk
                    tgt, cur = p.get(tk), p.get(dk)
                    if not tgt:
                        p[dk] = None
                    elif cur is None:
                        p[dk] = list(tgt)  # first sighting: appear right there
                        moving = True
                    else:
                        d = [tgt[i] - cur[i] for i in range(3)]
                        if d[0] * d[0] + d[1] * d[1] + d[2] * d[2] > 1e-8:
                            p[dk] = [cur[i] + d[i] * a for i in range(3)]
                            moving = True
            if moving:
                redraw()
    except Exception as e:
        print("[Stars] smooth error:", e)
    return 1.0 / 60.0


# ----------------------------------------------------------------------------
# Undo / redo
# Every change the sync code detects LOCALLY is recorded (remote changes never
# come through there, so your history only ever holds what YOU did). A burst of
# edits (a whole drag, a whole delete) becomes one step. The host picks the rule:
#   OWN    -> Ctrl+Z undoes your latest step
#   GLOBAL -> Ctrl+Z undoes the latest step in the room; if someone else made it,
#             the request is sent to them and their Blender undoes it.
# ----------------------------------------------------------------------------

def anim_playing():
    try:
        return any(w.screen.is_animation_playing for w in bpy.context.window_manager.windows)
    except Exception:
        return False


def log_change(kind, key, old, new, slow=False):
    now = time.time()
    if S["quiet"] or now < S["quiet_until"] or anim_playing():
        return
    if slow and not S["open"] and S["last_commit_id"] and now - S["last_commit_t"] < 1.0:
        a = S["acts"].get(S["last_commit_id"])
        h = S["hist"].get(S["last_commit_id"])
        if a is not None and h is not None and not a["undone"]:
            # slow pollers (materials, collections) lag a bit: glue onto the step that just happened
            h.append({"k": kind, "key": key, "old": old, "new": new})
            S["last_commit_t"] = now
            return
    if not S["open"]:
        S["open_start"] = now
    idx = S["open_idx"].get(key)
    if idx is None:
        S["open_idx"][key] = len(S["open"])
        S["open"].append({"k": kind, "key": key, "old": old, "new": new})
    else:
        c = S["open"][idx]
        if kind == "pr":
            c["old"] = {**old, **c["old"]}   # keep the FIRST old value of each property
            c["new"] = {**c["new"], **new}
        else:
            c["new"] = new
    S["open_t"] = now


def register_act(aid, author):
    S["acts"][aid] = {"a": author, "undone": False}
    S["order"].append(aid)
    if len(S["order"]) > MAX_UNDO * 4:
        S["acts"].pop(S["order"].pop(0), None)
    if S["rs"].get("undo") == "GLOBAL":
        S["redo_order"].clear()
    elif author == S["me"]:
        S["redo_order"] = [i for i in S["redo_order"] if S["acts"].get(i, {}).get("a") != S["me"]]


def set_undone(aid, u):
    a = S["acts"].get(aid)
    if not a:
        return
    a["undone"] = u
    if aid in S["redo_order"]:
        S["redo_order"].remove(aid)
    if u:
        S["redo_order"].append(aid)


def purge_author(pid):
    S["order"] = [i for i in S["order"] if S["acts"].get(i, {}).get("a") != pid]
    for i in [i for i, a in S["acts"].items() if a["a"] == pid]:
        S["acts"].pop(i, None)
    S["redo_order"] = [i for i in S["redo_order"] if i in S["acts"]]


def commit_open(net, force=False):
    if not S["open"]:
        return
    now = time.time()
    quiet_for = now - S["open_t"]
    age = now - S["open_start"]
    if not force:
        if S["mouse_down"] and age < 20.0:
            return                                   # still dragging / holding a button
        busy = modal_running()
        bnd = S["boundary"]
        if bnd > S["open_start"] - 0.3 and now - bnd >= 0.12 and not busy:
            pass                                     # a click / key action just ended: close the step
        elif quiet_for >= UNDO_GAP and not (busy and quiet_for < 3.0 and age < 8.0):
            pass                                     # things went quiet
        elif age >= 2.0 and not busy:
            pass                                     # safety: a step can never grow forever
        else:
            return
    S["boundary"] = 0.0
    changes = [c for c in S["open"] if c["old"] != c["new"]]
    S["open"], S["open_idx"] = [], {}
    if not changes:
        return
    aid = uuid.uuid4().hex[:8]
    S["hist"][aid] = changes
    while len(S["hist"]) > MAX_UNDO:
        S["hist"].pop(next(iter(S["hist"])))
    S["last_commit_id"], S["last_commit_t"] = aid, now
    register_act(aid, S["me"])
    net.send({"t": "act", "id": aid, "a": S["me"]})


def sync_now(net):
    """Catch up on anything you did in the last fraction of a second, so it is part of the history."""
    S["last_mesh_t"] = 0.0
    safe(sync_objects, net)
    safe(poll_props, net)
    safe(sync_meshes, net)
    safe(sync_transforms, net)
    safe(poll_slow, net)
    commit_open(net, force=True)


def apply_change(net, c, undo):
    k, key = c["k"], c["key"]
    v = c["old"] if undo else c["new"]
    me = S["me"]
    if k == "x":
        ob = bpy.data.objects.get(key[1])
        if ob and v:
            ob.location, ob.rotation_euler, ob.scale = v
            S["cache"][ob.name] = read_x(ob)  # read back so the sync loop doesn't re-send / re-log it
            net.send({"t": "x", "id": me, "o": [[ob.name, list(ob.location),
                                                 list(ob.rotation_euler), list(ob.scale)]]})
    elif k == "pr":
        ob = bpy.data.objects.get(key[1])
        if ob and v:
            apply_props(ob, v)
            new = full_props(ob)
            cache = S["pc"].setdefault(ob.name, {})
            for pk in v:
                if pk in new:
                    cache[pk] = new[pk]
            net.send({"t": "pr", "n": ob.name, "d": v})
    elif k == "md":
        ob = bpy.data.objects.get(key[1])
        if ob and v is not None:
            apply_list(ob, key[2], v)
            lst = lists_dump(ob, key[2])
            note_list(ob.name, key[2], lst)
            net.send({"t": "md", "n": ob.name, "k": key[2], "l": lst})
    elif k == "m":
        ob = bpy.data.objects.get(key[1])
        if ob and ob.type == 'MESH' and v:
            set_mesh(ob, v)
            net.send({"t": "m", "id": me, "n": ob.name, "d": v})
    elif k in ("add", "del"):
        make = (k == "del") == undo   # undoing a delete / redoing an add = bring it back
        if make:
            if v:
                apply_objects([v])
                net.send({"t": "add", "o": [v]})
        else:
            remove_obj(key[1])
            net.send({"t": "del", "n": [key[1]]})
    elif k == "mat":
        if v is not None:
            mat_apply(key[1], v)
            net.send({"t": "mat", "n": key[1], "d": v})
    elif k == "col":
        if v is not None:
            coll_apply(v)
            net.send({"t": "col", "d": v})


def settle(net):
    """After an undo/redo: let every sync check see the new state once, quietly, so the undo
    itself can never turn into a new history step (that is what made Ctrl+Z need many presses)."""
    S["last_mesh_t"] = 0.0
    safe(sync_objects, net)
    safe(poll_props, net)
    safe(sync_meshes, net)
    safe(sync_transforms, net)
    safe(poll_slow, net)


def run_action(aid, undo):
    """Undo (or redo) one of MY steps and tell everybody."""
    net = S["net"]
    changes = S["hist"].get(aid)
    if not net or not changes:
        return False
    # bring objects back first, change things in the middle, delete things last
    def is_make(c):
        return c["k"] in ("add", "del") and ((c["k"] == "del") == undo)

    def is_remove(c):
        return c["k"] in ("add", "del") and not is_make(c)

    mid = [c for c in changes if c["k"] not in ("add", "del")]
    if undo:
        mid.reverse()
    ordered = [c for c in changes if is_make(c)] + mid + [c for c in changes if is_remove(c)]
    S["quiet"] = True
    try:
        for c in ordered:
            try:
                apply_change(net, c, undo)
            except Exception as e:
                print("[Stars] undo step error:", e)
        settle(net)
    finally:
        S["quiet"] = False
        S["quiet_until"] = time.time() + 0.6   # slow pollers get one more quiet pass
    set_undone(aid, undo)
    net.send({"t": "ud", "id": aid, "u": undo})
    redraw()
    return True


def do_undo(redo=False):
    """Returns a message for the status bar, or None if there was nothing to do."""
    net = S["net"]
    if is_locked():
        return "The host turned editing off, so there is nothing to undo"
    sync_now(net)
    me = S["me"]
    # with editing off nobody else can have new changes, so only ever undo your own
    mine_only = S["rs"].get("undo") != "GLOBAL" or not S["rs"].get("edit", True)
    for aid in reversed(S["redo_order"] if redo else S["order"]):
        a = S["acts"].get(aid)
        if not a or a["undone"] != redo:
            continue
        if mine_only and a["a"] != me:
            continue
        if a["a"] == me:
            if run_action(aid, not redo):
                return "Redid your change" if redo else "Undid your change"
            S["acts"].pop(aid, None)  # its data is gone; skip it
            continue
        net.send({"t": "req", "id": aid, "to": a["a"], "do": "redo" if redo else "undo"})
        who = S["peers"].get(a["a"], {}).get("name", "player")
        return "Asked %s to %s their change" % (who, "redo" if redo else "undo")
    return None


# ----------------------------------------------------------------------------
# Viewport drawing: other players' selections, cursors and names
# ----------------------------------------------------------------------------

EDGES = ((0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
         (0, 4), (1, 5), (2, 6), (3, 7))


def _shader():
    for n in ('UNIFORM_COLOR', '3D_UNIFORM_COLOR'):
        try:
            return gpu.shader.from_builtin(n)
        except Exception:
            pass
    return None


def draw_3d():
    if not S["active"] or not S["peers"] or not bpy.context.window_manager.stars_show_cursors:
        return
    sh = _shader()
    if not sh:
        return
    gpu.state.blend_set('ALPHA')
    gpu.state.depth_test_set('NONE')
    try:
        gpu.state.line_width_set(2.5)
    except Exception:
        pass
    for p in S["peers"].values():
        pts = []
        for name in p["s"]:
            ob = bpy.data.objects.get(name)
            if not ob or not ob.visible_get():
                continue
            corners = [ob.matrix_world @ Vector(c) for c in ob.bound_box]
            for a, b in EDGES:
                pts += [corners[a], corners[b]]
        if shown(p, "c"):
            c = Vector(shown(p, "c"))
            for ax in ((0.25, 0, 0), (0, 0.25, 0), (0, 0, 0.25)):
                d = Vector(ax)
                pts += [c - d, c + d]
        if shown(p, "v"):
            e = Vector(shown(p, "v"))
            for ax in ((0.2, 0, 0), (0, 0.2, 0), (0, 0, 0.2)):
                d = Vector(ax)
                pts += [e - d, e + d]
            if shown(p, "f"):
                pts += [e, Vector(shown(p, "f"))]
        if pts:
            batch = batch_for_shader(sh, 'LINES', {"pos": [tuple(v) for v in pts]})
            sh.bind()
            sh.uniform_float("color", (p["color"][0], p["color"][1], p["color"][2], 1.0))
            batch.draw(sh)
    try:
        gpu.state.line_width_set(1.0)
    except Exception:
        pass
    gpu.state.blend_set('NONE')


def peer_tex(p):
    """Build (once) the GPU texture for a player's picture."""
    t = p.get("tex")
    if t is not None:
        return None if t is False else t
    p["tex"] = False
    av = p.get("av")
    if not av:
        return None
    try:
        w, h = av["w"], av["h"]
        raw = base64.b64decode(av["d"])
        buf = gpu.types.Buffer('FLOAT', w * h * 4, [b / 255.0 for b in raw])
        p["tex"] = gpu.types.GPUTexture((w, h), format='RGBA8', data=buf)
        p["tw"], p["th"] = w, h
    except Exception as e:
        print("[Stars] couldn't make picture:", e)
    return None if p["tex"] is False else p["tex"]


def draw_avatar(p, x, y):
    tex = peer_tex(p)
    if not tex:
        return
    sh = None
    for n in ('IMAGE', '2D_IMAGE'):
        try:
            sh = gpu.shader.from_builtin(n)
            break
        except Exception:
            pass
    if not sh:
        return
    k = AVATAR_PX / max(p["tw"], p["th"])
    w, h = p["tw"] * k, p["th"] * k
    batch = batch_for_shader(sh, 'TRI_FAN', {"pos": ((x, y), (x + w, y), (x + w, y + h), (x, y + h)),
                                             "texCoord": ((0, 0), (1, 0), (1, 1), (0, 1))})
    gpu.state.blend_set('ALPHA')
    sh.bind()
    sh.uniform_sampler("image", tex)
    batch.draw(sh)
    gpu.state.blend_set('NONE')


def draw_2d():
    if not S["active"] or not S["peers"] or not bpy.context.window_manager.stars_show_cursors:
        return
    region = bpy.context.region
    rv3d = bpy.context.region_data
    if not region or not rv3d:
        return
    try:
        blf.size(0, 15)
    except TypeError:
        blf.size(0, 15, 72)
    show_av = bpy.context.window_manager.stars_show_avatars
    for p in S["peers"].values():
        spots = []
        if shown(p, "c"):
            spots.append(Vector(shown(p, "c")))
        for name in p["s"][:3]:
            ob = bpy.data.objects.get(name)
            if ob:
                spots.append(ob.matrix_world.translation)
        if shown(p, "v"):
            spots.append(Vector(shown(p, "v")))
        for i, loc in enumerate(spots):
            pt = view3d_utils.location_3d_to_region_2d(region, rv3d, loc)
            if pt:
                if i == 0 and show_av and p.get("av"):
                    try:
                        draw_avatar(p, pt.x + 8, pt.y + 26)  # picture sits just above the name
                    except Exception as e:
                        print("[Stars] picture draw error:", e)
                blf.color(0, p["color"][0], p["color"][1], p["color"][2], 1.0)
                blf.position(0, pt.x + 8, pt.y + 8, 0)
                blf.draw(0, p["name"])


_handles = []


# ----------------------------------------------------------------------------
# Session control and UI
# ----------------------------------------------------------------------------

def end_session(status=""):
    net = S["net"]
    if net:
        try:
            if S["active"]:
                net.send({"t": "bye", "id": S["me"]})
        except Exception:
            pass
        net.stop()
    ips = S["ips"]
    S.clear()
    S.update(fresh_state())
    S["net"] = None
    S["ips"] = ips
    S["status"] = status
    rebuild_ui()
    redraw()


def my_hello(wm, host=False, room="", code=""):
    h = {"t": "hello", "id": S["me"], "name": wm.stars_name or "Player",
         "color": list(wm.stars_color)}
    if code:
        h["code"] = code
    if AVATAR["av"]:
        h["av"] = AVATAR["av"]
    if host:
        h["host"] = True
        h["room"] = room
    return h


def do_join(op, wm, host, port, code):
    end_session()
    net = Net()
    try:
        net.start_client(resolve_host(host), port)
    except Exception as e:
        op.report({'ERROR'}, "Couldn't reach %s:%d - %s. Check you copied the whole join code." % (host, port, e))
        return {'CANCELLED'}
    S["net"] = net
    S["me"] = uuid.uuid4().hex[:8]
    seed_caches()
    S["active"] = True
    S["status"] = "Joined"
    S["code"] = code
    net.send(my_hello(wm, code=code))
    return {'FINISHED'}


class STARS_OT_host(Operator):
    bl_idname = "stars.host"
    bl_label = "Host Room"

    def execute(self, context):
        wm = context.window_manager
        end_session()
        net = Net()
        port = wm.stars_port
        room = wm.stars_room or "My Room"
        short = gen_short()
        code = wm.stars_host_code.strip().upper() or gen_room_code()
        net.info = {"room": room, "short": short, "public": bool(wm.stars_public), "code": code,
                    "players": 1, "port": port}
        try:
            net.start_host(port)
        except OSError as e:
            self.report({'ERROR'}, "Couldn't open port %d: %s" % (port, e))
            return {'CANCELLED'}
        S["net"] = net
        S["me"] = uuid.uuid4().hex[:8]
        S["room"] = room
        S["short"] = short
        S["public"] = bool(wm.stars_public)
        seed_caches()
        addr = wm.stars_addr.strip() or lan_ip()
        net.info["ip"] = addr
        net.pub_evt.set()
        S["addr"], S["port"] = addr, port
        S["code"] = code
        wm.stars_hostinfo = "%s:%d" % (addr, port)
        net.hellos[S["me"]] = my_hello(wm, True, room)
        S["rs"]["undo"] = wm.stars_undo_mode
        S["rs"]["edit"] = bool(wm.stars_guest_edit)
        net.guest_edit = bool(wm.stars_guest_edit)
        S["active"] = True
        S["status"] = "Hosting"
        if wm.stars_relay:
            S["relay_status"] = "Easy connect: connecting..."
            start_relay(net, wm.stars_relay_host.strip() or "bore.pub", port)
        return {'FINISHED'}


def join_link():
    """One string that holds everything a friend needs: address:port/code"""
    return "%s:%d/%s" % (S["addr"], S["port"], S["code"])


class STARS_OT_join_link(Operator):
    bl_idname = "stars.join_link"
    bl_label = "Join Room"

    def execute(self, context):
        wm = context.window_manager
        text = wm.stars_join_link.strip()
        m = re.search(r"([A-Za-z0-9][A-Za-z0-9.\-]*):(\d{1,5})(?:/([A-Za-z0-9]+))?", text)
        code = ""
        try:
            host, port, code = m.group(1), int(m.group(2)), (m.group(3) or "")
            assert 1 <= port <= 65535
        except Exception:
            self.report({'ERROR'}, "That join code doesn't look right. Paste the whole thing, like bore.pub:12345/ABC123")
            return {'CANCELLED'}
        return do_join(self, wm, host, port, code.upper())


class STARS_OT_join(Operator):
    bl_idname = "stars.join"
    bl_label = "Join Room"

    def execute(self, context):
        wm = context.window_manager
        host, port = wm.stars_join_ip.strip(), wm.stars_join_port
        if ":" in host:  # allow pasting "ip:port"
            host, p = host.rsplit(":", 1)
            try:
                port = int(p)
            except ValueError:
                pass
        code = wm.stars_join_code.strip().upper()
        if not host:
            self.report({'ERROR'}, "Type the host's IP address")
            return {'CANCELLED'}
        if not code:
            self.report({'ERROR'}, "Type the room code")
            return {'CANCELLED'}
        return do_join(self, wm, host, port, code)


class STARS_OT_join_addr(Operator):
    bl_idname = "stars.join_addr"
    bl_label = "Join"
    host: StringProperty()
    port: IntProperty()

    def execute(self, context):
        return do_join(self, context.window_manager, self.host, self.port,
                       "%s:%d" % (self.host, self.port))


class STARS_OT_scan(Operator):
    bl_idname = "stars.scan"
    bl_label = "Refresh"

    def execute(self, context):
        start_scan()
        return {'FINISHED'}


class STARS_OT_leave(Operator):
    bl_idname = "stars.leave"
    bl_label = "Leave Room"

    def execute(self, context):
        end_session("Left room")
        return {'FINISHED'}


class STARS_OT_copy(Operator):
    bl_idname = "stars.copy"
    bl_label = "Copy"
    bl_description = "Copy to clipboard"
    what: StringProperty()

    def execute(self, context):
        v = {"code": S["code"], "short": S["short"], "ip": S["addr"], "port": str(S["port"]),
             "all": "Host IP: %s\nPort: %d\nRoom code: %s" % (S["addr"], S["port"], S["code"]),
             "link": join_link()
             }.get(self.what, "")
        context.window_manager.clipboard = v
        self.report({'INFO'}, "Copied")
        return {'FINISHED'}


class STARS_OT_kick(Operator):
    bl_idname = "stars.kick"
    bl_label = "Kick"
    bl_description = "Kick this player out of the room (host only)"
    pid: StringProperty()

    def execute(self, context):
        net = S["net"]
        if net and net.is_host and self.pid in S["peers"]:
            name = S["peers"][self.pid]["name"]
            net.kick(self.pid)
            S["peers"].pop(self.pid, None)
            net.hellos.pop(self.pid, None)
            net.send({"t": "bye", "id": self.pid})
            rebuild_ui()
            redraw()
            self.report({'INFO'}, "Kicked %s" % name)
        return {'FINISHED'}


class STARS_OT_show_ips(Operator):
    bl_idname = "stars.show_ips"
    bl_label = "Show My IPs"
    bl_description = "List this computer's IP addresses so you know what to put as Host IP"

    def execute(self, context):
        S["ips"] = local_ips()
        return {'FINISHED'}


class STARS_OT_public_ip(Operator):
    bl_idname = "stars.public_ip"
    bl_label = "Find Public IP"
    bl_description = "Ask api.ipify.org for your public IP (needs port forwarding to be useful)"

    def execute(self, context):
        try:
            ip = urllib.request.urlopen("https://api.ipify.org", timeout=4).read().decode().strip()
        except Exception as e:
            self.report({'ERROR'}, "Couldn't look up public IP: %s" % e)
            return {'CANCELLED'}
        S["ips"] = [x for x in S["ips"] if x[1] != "public (internet)"] + [(ip, "public (internet)")]
        context.window_manager.stars_addr = ip  # fill it in for you
        self.report({'INFO'}, "Your public IP is %s" % ip)
        return {'FINISHED'}


class STARS_OT_upnp(Operator):
    bl_idname = "stars.upnp"
    bl_label = "Open Port Automatically"
    bl_description = ("Ask your router (UPnP) to forward the port so friends over the internet can reach you. "
                      "Blender may freeze for a few seconds")

    def execute(self, context):
        wm = context.window_manager
        try:
            ext = upnp_open(wm.stars_port, lan_ip())
        except Exception as e:
            self.report({'ERROR'}, "Router said no (%s). Forward the port by hand, or use Tailscale." % e)
            return {'CANCELLED'}
        if ext and ip_tag(ext) != "public":
            self.report({'WARNING'}, "Port opened, but your ISP shares your IP (%s), so friends can't reach it. "
                                     "Use Tailscale instead." % ext)
            return {'FINISHED'}
        if ext:
            wm.stars_addr = ext
        self.report({'INFO'}, "Port %d opened%s" % (wm.stars_port, " - your IP is " + ext if ext else
                                                    ". Now press Find Public IP"))
        return {'FINISHED'}


class STARS_OT_use_ip(Operator):
    bl_idname = "stars.use_ip"
    bl_label = "Use"
    ip: StringProperty()

    def execute(self, context):
        context.window_manager.stars_addr = self.ip
        return {'FINISHED'}


class STARS_OT_pick_avatar(Operator):
    bl_idname = "stars.pick_avatar"
    bl_label = "Upload PNG"
    bl_description = "Pick a PNG picture. Other players see it next to your name (shrunk to 64 px)"
    filepath: StringProperty(subtype='FILE_PATH')
    filter_glob: StringProperty(default="*.png", options={'HIDDEN'})

    def invoke(self, context, event):
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}

    def execute(self, context):
        try:
            av = make_avatar(self.filepath)
        except Exception as e:
            self.report({'ERROR'}, "Couldn't use that picture: %s" % e)
            return {'CANCELLED'}
        set_avatar(av)
        self.report({'INFO'}, "Picture set (%dx%d)" % (av["w"], av["h"]))
        return {'FINISHED'}


class STARS_OT_clear_avatar(Operator):
    bl_idname = "stars.clear_avatar"
    bl_label = "Remove"
    bl_description = "Stop using a picture"

    def execute(self, context):
        set_avatar(None)
        return {'FINISHED'}


class STARS_OT_watch(Operator):
    bl_idname = "stars.watch"
    bl_label = "Stars input watcher"
    bl_options = {'INTERNAL'}

    def invoke(self, context, event):
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def modal(self, context, event):
        if not S["active"]:
            S["mouse_down"] = False
            return {'FINISHED', 'PASS_THROUGH'}
        t, v = event.type, event.value
        if t in {'LEFTMOUSE', 'RIGHTMOUSE', 'MIDDLEMOUSE'}:
            if v == 'PRESS':
                S["mouse_down"] = True
            elif v == 'RELEASE':
                S["mouse_down"] = False
                S["boundary"] = time.time()
        elif t == 'WINDOW_DEACTIVATE':
            S["mouse_down"] = False
        elif v == 'RELEASE' and t not in {'MOUSEMOVE', 'INBETWEEN_MOUSEMOVE', 'TIMER', 'NONE'} \
                and "MOUSE" not in t and "TIMER" not in t:
            S["boundary"] = time.time()
        return {'PASS_THROUGH'}


class STARS_OT_undo(Operator):
    bl_idname = "stars.undo"
    bl_label = "Undo (Stars)"
    bl_description = "Undo using the room's Ctrl+Z rule"
    redo: BoolProperty(default=False)

    def invoke(self, context, event):
        if not (S["active"] and S["net"]):
            return {'PASS_THROUGH'}  # not in a room: normal Blender undo
        try:
            msg = do_undo(self.redo)
        except Exception as e:
            print("[Stars] undo error:", e)
            msg = None
        self.report({'INFO'}, msg or ("Nothing to redo" if self.redo else "Nothing to undo"))
        return {'FINISHED'}


_keymaps = []


def register_keys():
    kc = bpy.context.window_manager.keyconfigs.addon
    if not kc:
        return
    km = kc.keymaps.new(name="Screen", space_type='EMPTY')
    for mod in ({"ctrl": True}, {"oskey": True}):  # Ctrl on Win/Linux, Cmd on Mac
        for shift, redo in ((False, False), (True, True)):
            kmi = km.keymap_items.new("stars.undo", 'Z', 'PRESS', shift=shift, **mod)
            kmi.properties.redo = redo
            _keymaps.append((km, kmi))


def unregister_keys():
    for km, kmi in _keymaps:
        try:
            km.keymap_items.remove(kmi)
        except Exception:
            pass
    _keymaps.clear()


class StarsPeer(PropertyGroup):
    color: FloatVectorProperty(subtype='COLOR', size=3, min=0.0, max=1.0)
    pid: StringProperty()


TAB_ITEMS = [
    ('ROOM', "Room", "Host or join a room"),
    ('BROWSE', "Browse", "Find public rooms"),
    ('PLAYERS', "Players", "Who is in the room"),
    ('SETTINGS', "Settings", "Sync options"),
    ('CREDITS', "Credits", "About this addon"),
]


UNDO_ITEMS = [
    ('OWN', "Only my changes", "Ctrl+Z only undoes things you made yourself"),
    ('GLOBAL', "Everyone's changes", "Ctrl+Z undoes the latest change in the room, whoever made it"),
]


def _undo_mode_changed(self, context):
    net = S["net"]
    if S["active"] and net and net.is_host:
        S["rs"]["undo"] = self.stars_undo_mode
        net.send({"t": "rs", "d": dict(S["rs"])})  # tell everybody


def _guest_edit_changed(self, context):
    net = S["net"]
    if S["active"] and net and net.is_host:
        net.guest_edit = bool(self.stars_guest_edit)
        S["rs"]["edit"] = bool(self.stars_guest_edit)
        net.send({"t": "rs", "d": dict(S["rs"])})  # tell everybody


def _public_changed(self, context):
    net = S["net"]
    if S["active"] and net and net.is_host:
        S["public"] = bool(self.stars_public)
        net.info["public"] = bool(self.stars_public)
        net.pub_evt.set()  # announce (or un-announce) right now


def _profile_changed(self, context):
    if _loading_prefs[0]:
        return
    save_prefs(self)   # remembered next time you open Blender
    push_profile(self)  # and the room sees it right away


def _tab_changed(self, context):
    if self.stars_tab == 'BROWSE':
        start_scan()


class STARS_PT_panel(Panel):
    bl_label = "Stars Multiplayer"
    bl_idname = "STARS_PT_panel"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Stars"

    def draw(self, context):
        wm = context.window_manager
        self.layout.prop(wm, "stars_tab", expand=True)
        col = self.layout.column()
        getattr(self, "tab_" + wm.stars_tab.lower())(wm, col)

    def tab_room(self, wm, col):
        net = S["net"]
        if not S["active"]:
            # --- You -------------------------------------------------------
            box = col.box()
            box.label(text="You", icon='USER')
            box.prop(wm, "stars_name", text="Name")
            box.prop(wm, "stars_color", text="Color")
            self.avatar_row(box)
            # --- Join ------------------------------------------------------
            box = col.box()
            box.label(text="Join a room", icon='IMPORT')
            box.prop(wm, "stars_join_link", text="Join code")
            box.label(text="Paste the code your friend sent you.")
            box.operator("stars.join_link", icon='PLAY')
            box.label(text="Public rooms: see the Browse tab.")
            # --- Host ------------------------------------------------------
            box = col.box()
            box.label(text="Host a room", icon='ADD')
            box.prop(wm, "stars_room", text="Room name")
            box.prop(wm, "stars_host_code", text="Room code")
            box.prop(wm, "stars_public")
            box.prop(wm, "stars_relay")
            box.label(text="Easy connect: works from anywhere,")
            box.label(text="no router or port setup needed.")
            box.operator("stars.host", icon='WORLD')
            if S["status"]:
                col.label(text=S["status"], icon='INFO')
            # --- Advanced --------------------------------------------------
            box = col.box()
            box.prop(wm, "stars_adv", icon='TRIA_DOWN' if wm.stars_adv else 'TRIA_RIGHT', emboss=False)
            if wm.stars_adv:
                box.label(text="Join by hand", icon='IMPORT')
                box.prop(wm, "stars_join_ip", text="Host IP")
                box.prop(wm, "stars_join_port", text="Port")
                box.prop(wm, "stars_join_code", text="Room code")
                box.operator("stars.join", icon='PLAY')
                box.separator()
                box.label(text="Hosting by hand (no Easy connect)", icon='PREFERENCES')
                box.prop(wm, "stars_port", text="Port")
                box.prop(wm, "stars_addr", text="Your IP")
                r = box.row(align=True)
                r.operator("stars.public_ip", text="Find Public IP", icon='URL')
                r.operator("stars.show_ips", text="My IPs", icon='VIEWZOOM')
                for ip, tag in S["ips"]:
                    row = box.row()
                    row.label(text="%s  (%s)" % (ip, tag))
                    row.operator("stars.use_ip", text="Use").ip = ip
                box.operator("stars.upnp", icon='PLUGIN')
        else:
            is_host = bool(net and net.is_host)
            box = col.box()
            box.label(text="Room: %s" % (S["room"] or "..."), icon='WORLD')
            if is_host:
                box = col.box()
                box.label(text="Invite friends", icon='EXPORT')
                row = box.row(align=True)
                row.label(text="Getting your join code..." if S["relay_status"].endswith("connecting...") else join_link())
                row.operator("stars.copy", text="", icon='COPYDOWN').what = "link"
                box.label(text="Send this join code to your friend.")
                if S["relay_status"]:
                    box.label(text=S["relay_status"], icon='WORLD' if S["relay_status"].endswith("on") else 'INFO')
                if S["lan"]:
                    box.label(text="Same Wi-Fi: %s : %d" % S["lan"])
                box = col.box()
                box.label(text="Visibility", icon='VIEWZOOM')
                box.prop(wm, "stars_public")
                if wm.stars_public:
                    box.label(text="Listed in Browse. No code needed.", icon='WORLD')
            else:
                box = col.box()
                box.label(text="Connected as a guest", icon='USER')
            col.separator()
            col.operator("stars.leave", icon='CANCEL')

    def avatar_row(self, col):
        av = AVATAR["av"]
        col.label(text="Your picture: %s" % ("%dx%d" % (av["w"], av["h"]) if av else "none"),
                  icon='IMAGE_DATA')
        row = col.row(align=True)
        row.operator("stars.pick_avatar", text="Upload PNG", icon='FILEBROWSER')
        row.operator("stars.clear_avatar", text="Remove", icon='X')

    def tab_players(self, wm, col):
        net = S["net"]
        if not S["active"]:
            col.label(text="Host or join a room first.", icon='INFO')
            return
        is_host = bool(net and net.is_host)
        col.label(text="In this room:", icon='COMMUNITY')
        row = col.row(align=True)
        row.prop(wm, "stars_color", text="")
        row.prop(wm, "stars_name", text="")
        col.label(text="That's you%s. Change name/color any time." % (" (host)" if is_host else ""))
        for it in wm.stars_peers:
            row = col.row()
            sub = row.row()
            sub.enabled = False
            sub.prop(it, "color", text="")
            row.label(text=it.name)
            if is_host:
                row.operator("stars.kick", text="", icon='X').pid = it.pid
        if is_host and len(wm.stars_peers):
            col.label(text="Click X to kick a player")

    def tab_browse(self, wm, col):
        col.label(text="Public rooms on your network", icon='WORLD')
        col.operator("stars.scan", icon='FILE_REFRESH',
                     text="Scanning..." if SCAN["busy"] else "Refresh")
        rooms = [r for r in SCAN["rooms"] if not (S["active"] and r.get("short") == S["short"])]
        if not rooms:
            col.label(text="No public rooms found")
        for r in rooms:
            box = col.box()
            row = box.row()
            row.label(text="%s  (%d here)" % (r.get("room") or "Room", r.get("players", 1)),
                      icon='USER')
            op = row.operator("stars.join_addr", text="Join")
            op.host = r["ip"]
            op.port = int(r["port"])
        col.separator()
        lan = {r.get("short") for r in rooms}
        far = [r for r in SCAN["net_rooms"]
               if r.get("short") not in lan and not (S["active"] and r.get("short") == S["short"])]
        col.label(text="Public rooms on the internet", icon='URL')
        if SCAN["err"]:
            col.label(text="Couldn't reach the board", icon='ERROR')
        elif not far:
            col.label(text="No public rooms found")
        for r in far:
            box = col.box()
            row = box.row()
            row.label(text="%s  (%d here)" % (r.get("room") or "Room", r.get("players", 1)), icon='USER')
            op = row.operator("stars.join_addr", text="Join")
            op.host = r["ip"]
            op.port = int(r["port"])
        col.separator()
        col.label(text="Private room? Use the Room tab")
        col.label(text="with the IP and room code.")

    def tab_settings(self, wm, col):
        net = S["net"]
        can_edit = (not S["active"]) or bool(net and net.is_host)
        box = col.box()
        box.label(text="Room settings (host only)", icon='LOCKED')
        if can_edit:
            box.prop(wm, "stars_undo_mode", text="Ctrl+Z")
            box.prop(wm, "stars_guest_edit")
            box.label(text="Applies to everyone in the room." if S["active"]
                      else "Used when you host a room.")
        else:
            names = {i[0]: i[1] for i in UNDO_ITEMS}
            row = box.row()
            row.enabled = False
            row.label(text="Ctrl+Z: " + names.get(S["rs"].get("undo", "OWN"), "?"))
            row = box.row()
            row.enabled = False
            row.label(text="Guests can edit: " + ("Yes" if S["rs"].get("edit", True) else "No"))
            box.label(text="Only the host can change these.")
        box = col.box()
        box.label(text="Your settings (only you)", icon='USER')
        box.prop(wm, "stars_show_cursors")
        box.prop(wm, "stars_show_avatars")
        box.prop(wm, "stars_relay_host", text="Relay")
        self.avatar_row(box)
        box.prop(wm, "stars_sync_materials")
        box.prop(wm, "stars_sync_scene")

    def tab_credits(self, wm, col):
        box = col.box()
        box.label(text="Stars Multiplayer", icon='SOLO_ON')
        box.label(text="Version 0.9.1")
        box.label(text="Made by herixd3")
        col.separator()
        box = col.box()
        box.label(text="Copyright (c) 2026 herixd3.")
        box.label(text="All rights reserved.")
        box.label(text="Provided \"as is\", without warranty")
        box.label(text="of any kind. Do not copy or resell")
        box.label(text="without permission from the author.")
        col.separator()
        col.label(text="Blender is a registered trademark of")
        col.label(text="the Blender Foundation. This addon is")
        col.label(text="not affiliated with or endorsed by it.")


classes = (StarsPeer, STARS_OT_watch, STARS_OT_join_link, STARS_OT_pick_avatar, STARS_OT_clear_avatar, STARS_OT_undo, STARS_OT_upnp, STARS_OT_host, STARS_OT_join, STARS_OT_join_addr, STARS_OT_scan,
           STARS_OT_leave, STARS_OT_copy, STARS_OT_kick, STARS_OT_show_ips,
           STARS_OT_public_ip, STARS_OT_use_ip, STARS_PT_panel)


def register():
    for c in classes:
        bpy.utils.register_class(c)
    WM = bpy.types.WindowManager
    WM.stars_name = StringProperty(name="Name", default="Player", update=_profile_changed)
    WM.stars_color = FloatVectorProperty(name="Color", subtype='COLOR', size=3,
                                         min=0.0, max=1.0, default=(0.2, 0.7, 1.0),
                                         update=_profile_changed)
    WM.stars_room = StringProperty(name="Room name", default="My Room")
    WM.stars_addr = StringProperty(
        name="Host IP",
        description="Leave blank for same Wi-Fi. For internet play use your VPN/public IP (see Show My IPs)",
        default="")
    WM.stars_port = IntProperty(name="Port", default=DEFAULT_PORT, min=1024, max=65535)
    WM.stars_join = StringProperty(name="Code", description="Room code (or host:port)")
    WM.stars_peers = CollectionProperty(type=StarsPeer)
    WM.stars_tab = EnumProperty(name="Tab", items=TAB_ITEMS, default='ROOM', update=_tab_changed)
    WM.stars_public = BoolProperty(
        name="Make room public",
        description="List this room for anyone to find (Wi-Fi and internet). No room code needed to join. "
                    "Your IP address is shown in the listing. Can be switched on or off while hosting",
        default=False, update=_public_changed)
    WM.stars_hostinfo = StringProperty(name="Host IP", default="")
    WM.stars_join_ip = StringProperty(name="Host IP", description="The IP address the host gives you", default="")
    WM.stars_join_port = IntProperty(name="Port", default=DEFAULT_PORT, min=1024, max=65535)
    WM.stars_join_link = StringProperty(name="Join code", description="Paste the join code your friend sent", default="")
    WM.stars_adv = BoolProperty(name="Advanced (connect by hand)", default=False)
    WM.stars_join_code = StringProperty(name="Room code", description="The room code the host gives you", default="")
    WM.stars_host_code = StringProperty(name="Room code", description="Leave blank for a random one", default="")
    WM.stars_undo_mode = EnumProperty(name="Ctrl+Z", items=UNDO_ITEMS, default='OWN',
                                      update=_undo_mode_changed)
    WM.stars_show_cursors = BoolProperty(name="Show other players' cursors", default=True)
    WM.stars_show_avatars = BoolProperty(name="Show player pictures", default=True)
    WM.stars_relay = BoolProperty(
        name="Easy connect (no port forwarding)",
        description="Gets a public address through a free relay so friends can join from anywhere. "
                    "Your room's data passes through that relay unencrypted",
        default=True)
    WM.stars_relay_host = StringProperty(name="Relay server", default="bore.pub",
                                         description="Address of the bore relay used by Easy connect")
    WM.stars_guest_edit = BoolProperty(
        name="Guests can edit",
        description="Off = guests are view-only: they can't move, scale or edit meshes, materials, etc.",
        default=True, update=_guest_edit_changed)
    WM.stars_sync_materials = BoolProperty(name="Sync materials", default=True)
    WM.stars_sync_scene = BoolProperty(name="Sync scene and world settings", default=True)
    _handles.append(bpy.types.SpaceView3D.draw_handler_add(draw_3d, (), 'WINDOW', 'POST_VIEW'))
    _handles.append(bpy.types.SpaceView3D.draw_handler_add(draw_2d, (), 'WINDOW', 'POST_PIXEL'))
    bpy.app.handlers.depsgraph_update_post.append(on_depsgraph)
    bpy.app.timers.register(tick, first_interval=0.5)
    bpy.app.timers.register(smooth_tick, first_interval=0.5)
    load_avatar()
    bpy.app.timers.register(_load_prefs_timer, first_interval=0.2)  # restore saved name + color
    register_keys()


def unregister():
    end_session()
    unregister_keys()
    if bpy.app.timers.is_registered(smooth_tick):
        bpy.app.timers.unregister(smooth_tick)
    if bpy.app.timers.is_registered(tick):
        bpy.app.timers.unregister(tick)
    if on_depsgraph in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.remove(on_depsgraph)
    for h in _handles:
        bpy.types.SpaceView3D.draw_handler_remove(h, 'WINDOW')
    _handles.clear()
    WM = bpy.types.WindowManager
    for p in ("stars_name", "stars_color", "stars_room", "stars_addr",
              "stars_port", "stars_join", "stars_peers", "stars_tab", "stars_public",
              "stars_hostinfo", "stars_join_ip", "stars_join_port", "stars_join_code",
              "stars_host_code", "stars_undo_mode", "stars_show_cursors", "stars_sync_materials",
              "stars_sync_scene", "stars_show_avatars", "stars_guest_edit", "stars_relay", "stars_relay_host", "stars_join_link", "stars_adv"):
        if hasattr(WM, p):
            delattr(WM, p)
    for c in reversed(classes):
        bpy.utils.unregister_class(c)


if __name__ == "__main__":
    register()
