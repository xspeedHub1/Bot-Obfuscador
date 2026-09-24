# Cebo_deobf_bot.py
# Handles: Luraph v15 (bytecode VM) + Luarmor (source VM wrapper)
# deps: pip install discord.py aiohttp

import discord
from discord.ext import commands
from discord import app_commands
import re, io, base64, struct, os, json, textwrap
from typing import Optional, Tuple
from enum import Enum, auto
import aiohttp

TOKEN  = os.environ.get("DISCORD_TOKEN", "YOUR_BOT_TOKEN")
PREFIX = "!"

# ══════════════════════════════════════════════════════════════════
#  OBFUSCATOR DETECTION
# ══════════════════════════════════════════════════════════════════

class ObfType(Enum):
    LURAPH_V15 = auto()
    LUARMOR    = auto()
    GENERIC    = auto()
    UNKNOWN    = auto()

LURAPH_SIGS = [
    r'local\s+\w+\s*=\s*\{\s*\[0\]\s*=\s*function',
    r'string\.byte\s*\(\w+\s*,\s*\w+\s*,\s*\w+\s*\)',
    r'bit32\.(band|rshift)\s*\(\s*\w+\s*,\s*(?:0x[\da-fA-F]+|\d+)\s*\)',
    r'local\s+\w+\s*=\s*\{\s*\w+\s*,\s*\w+\s*,\s*\w+\s*,\s*\w+\s*\}',
    r'"[A-Za-z0-9+/\\x]{200,}"',
    r'local\s+\w+\s*=\s*\{\}\s*\n.*?local\s+\w+\s*=\s*\{\}',
]

LURAPH_SCORE_FLOOR  = 45

LUARMOR_SIGS = [
    r'loadstring\s*\(',
    r'load\s*\(\s*(?:table\.concat|string\.char)',
    r'for\s+\w+\s*=\s*1\s*,\s*#\w+\s*do',
    r'string\.char\s*\(table\.unpack',
    r'bit32\.(bxor|band)',
    r'local\s+\w+\s*=\s*\{[^\}]{400,}\}',
]

def identify(source: str) -> Tuple[ObfType, int]:
    lraph_score = sum(
        20 for p in LURAPH_SIGS
        if re.search(p, source, re.DOTALL | re.IGNORECASE)
    )
    larmor_score = sum(
        15 for p in LUARMOR_SIGS
        if re.search(p, source, re.DOTALL | re.IGNORECASE)
    )

    first_line = source.strip().split('\n')[0]
    if re.match(r'^local\s+\w+\s*=\s*"[A-Za-z0-9+/\\]{100,}"', first_line):
        lraph_score += 30

    if lraph_score >= LURAPH_SCORE_FLOOR and lraph_score > larmor_score:
        return ObfType.LURAPH_V15, lraph_score
    if larmor_score >= 30:
        return ObfType.LUARMOR, larmor_score
    if lraph_score > 0 or larmor_score > 0:
        return ObfType.GENERIC, max(lraph_score, larmor_score)
    return ObfType.UNKNOWN, 0

LUA51_MAGIC = b'\x1bLua'

LUA51_OPCODES = [
    'MOVE','LOADK','LOADBOOL','LOADNIL','GETUPVAL','GETGLOBAL','GETTABLE',
    'SETGLOBAL','SETUPVAL','SETTABLE','NEWTABLE','SELF','ADD','SUB','MUL',
    'DIV','MOD','POW','UNM','NOT','LEN','CONCAT','JMP','EQ','LT','LE',
    'TEST','TESTSET','CALL','TAILCALL','RETURN','FORLOOP','FORPREP',
    'TFORLOOP','SETLIST','CLOSE','CLOSURE','VARARG',
]

class BytecodeReader:
    def __init__(self, data: bytes):
        self.data = data
        self.pos  = 0

    def read(self, n: int) -> bytes:
        chunk = self.data[self.pos:self.pos + n]
        self.pos += n
        return chunk

    def byte(self) -> int:
        return struct.unpack('B', self.read(1))[0]

    def uint(self, sz: int = 4) -> int:
        fmt = {1:'B',2:'H',4:'I',8:'Q'}[sz]
        return struct.unpack('<' + fmt, self.read(sz))[0]

    def double(self) -> float:
        return struct.unpack('<d', self.read(8))[0]

    def lua_string(self) -> Optional[str]:
        sz = self.uint(4)
        if sz == 0:
            return None
        raw = self.read(sz)
        return raw.rstrip(b'\x00').decode('utf-8', errors='replace')

    def remaining(self) -> int:
        return len(self.data) - self.pos

class LuaProto:
    def __init__(self):
        self.source:     str          = ''
        self.line_start: int          = 0
        self.line_end:   int          = 0
        self.num_upvals: int          = 0
        self.num_params: int          = 0
        self.is_vararg:  int          = 0
        self.max_stack:  int          = 0
        self.instrs:     list         = []
        self.constants:  list         = []
        self.protos:     list         = []
        self.locals:     list[str]    = []
        self.upvalues:   list[str]    = []
        self.strings:    list[str]    = []
        self.numbers:    list[float]  = []

def parse_proto(r: BytecodeReader) -> LuaProto:
    p = LuaProto()
    p.source     = r.lua_string() or '?'
    p.line_start = r.uint()
    p.line_end   = r.uint()
    p.num_upvals = r.byte()
    p.num_params = r.byte()
    p.is_vararg  = r.byte()
    p.max_stack  = r.byte()

    n = r.uint()
    for _ in range(n):
        raw = r.uint()
        op  = raw & 0x3F
        a   = (raw >>  6) & 0xFF
        b   = (raw >> 23) & 0x1FF
        c   = (raw >> 14) & 0x1FF
        bx  = (raw >> 14) & 0x3FFFF
        sbx = bx - (0x3FFFF >> 1)
        opname = LUA51_OPCODES[op] if op < len(LUA51_OPCODES) else f'OP_{op}'
        p.instrs.append((opname, a, b, c, bx, sbx))

    n = r.uint()
    for _ in range(n):
        t = r.byte()
        if t == 0:
            p.constants.append(None)
        elif t == 1:
            p.constants.append(bool(r.byte()))
        elif t == 3:
            val = r.double()
            p.constants.append(val)
            p.numbers.append(val)
        elif t == 4:
            s = r.lua_string()
            p.constants.append(s)
            if s:
                p.strings.append(s)
        else:
            p.constants.append(f'<type{t}>')

    n = r.uint()
    for _ in range(n):
        p.protos.append(parse_proto(r))

    n = r.uint()
    r.read(n * 4)

    n = r.uint()
    for _ in range(n):
        name = r.lua_string() or '_'
        r.uint(); r.uint()
        p.locals.append(name)

    n = r.uint()
    for _ in range(n):
        name = r.lua_string() or '_upv'
        p.upvalues.append(name)

    return p

def parse_lua51(data: bytes) -> Optional[LuaProto]:
    if not data.startswith(LUA51_MAGIC):
        return None
    r = BytecodeReader(data)
    r.read(4)
    r.byte()
    r.byte()
    r.byte()
    r.byte()
    r.byte()
    r.byte()
    r.byte()
    r.byte()
    return parse_proto(r)

def collect_strings(proto: LuaProto, out: list, depth: int = 0):
    prefix = '  ' * depth
    for s in proto.strings:
        if s and len(s) > 1:
            out.append((depth, s))
    for child in proto.protos:
        collect_strings(child, out, depth + 1)

def reconstruct_from_proto(proto: LuaProto, indent: int = 0) -> str:
    pad   = '  ' * indent
    lines = []

    src = proto.source if proto.source != '?' else 'unknown'
    lines.append(f'{pad}-- function @ {src} '
                 f'[params={proto.num_params} upvals={proto.num_upvals} '
                 f'stack={proto.max_stack}]')

    for uv in proto.upvalues:
        lines.append(f'{pad}-- upvalue: {uv}')

    declared_locals = set()
    for name in proto.locals:
        if name and name not in declared_locals:
            lines.append(f'{pad}local {name}')
            declared_locals.add(name)

    for (op, a, b, c, bx, sbx) in proto.instrs:
        kst = proto.constants

        if op == 'GETGLOBAL':
            g = kst[bx] if bx < len(kst) else '?'
            local = proto.locals[a] if a < len(proto.locals) else f'R{a}'
            lines.append(f'{pad}{local} = {g}')

        elif op == 'SETGLOBAL':
            g     = kst[bx] if bx < len(kst) else '?'
            local = proto.locals[a] if a < len(proto.locals) else f'R{a}'
            lines.append(f'{pad}{g} = {local}')

        elif op == 'LOADK':
            val   = kst[bx] if bx < len(kst) else '?'
            local = proto.locals[a] if a < len(proto.locals) else f'R{a}'
            val_r = f'"{val}"' if isinstance(val, str) else str(val)
            lines.append(f'{pad}{local} = {val_r}')

        elif op == 'CALL':
            fn    = proto.locals[a] if a < len(proto.locals) else f'R{a}'
            nargs = b - 1
            lines.append(f'{pad}{fn}({"..." if nargs < 0 else f"{nargs} args"})')

        elif op == 'RETURN':
            if b == 1:
                lines.append(f'{pad}return')
            elif b == 2:
                ret = proto.locals[a] if a < len(proto.locals) else f'R{a}'
                lines.append(f'{pad}return {ret}')

        elif op == 'JMP':
            lines.append(f'{pad}-- jmp {sbx:+d}')

        elif op == 'CLOSURE':
            local = proto.locals[a] if a < len(proto.locals) else f'R{a}'
            lines.append(f'{pad}local function {local}()  -- closure proto[{bx}]')
            lines.append(f'{pad}end')

        elif op in ('EQ','LT','LE'):
            lhs = proto.locals[b & 0xFF] if (b & 0xFF) < len(proto.locals) else f'R{b}'
            rhs = proto.locals[c & 0xFF] if (c & 0xFF) < len(proto.locals) else f'R{c}'
            lines.append(f'{pad}-- {op} {lhs}, {rhs}')

    for i, child in enumerate(proto.protos):
        lines.append(f'\n{pad}-- ── nested function [{i}] ──')
        lines.append(reconstruct_from_proto(child, indent + 1))

    return '\n'.join(lines)

def extract_luraph_blob(source: str) -> Optional[bytes]:
    m = re.search(
        r'local\s+\w+\s*=\s*"((?:[^"\\]|\\.){100,})"',
        source
    )
    if not m:
        m = re.search(r'"((?:[^"\\]|\\.){200,})"', source)
    if not m:
        return None

    raw = m.group(1)

    def decode_lua_escapes(s: str) -> bytes:
        result = bytearray()
        i = 0
        while i < len(s):
            if s[i] == '\\' and i + 1 < len(s):
                nxt = s[i+1]
                if nxt.isdigit():
                    j = i + 1
                    while j < len(s) and j < i + 4 and s[j].isdigit():
                        j += 1
                    result.append(int(s[i+1:j]) & 0xFF)
                    i = j
                elif nxt == 'x':
                    result.append(int(s[i+2:i+4], 16))
                    i += 4
                elif nxt == 'n':
                    result.append(0x0A); i += 2
                elif nxt == 'r':
                    result.append(0x0D); i += 2
                elif nxt == '\\':
                    result.append(0x5C); i += 2
                elif nxt == '"':
                    result.append(0x22); i += 2
                else:
                    result.append(ord(nxt)); i += 2
            else:
                result.append(ord(s[i]) & 0xFF)
                i += 1
        return bytes(result)

    decoded = decode_lua_escapes(raw)

    if decoded[:4] == LUA51_MAGIC:
        return decoded

    try:
        b = base64.b64decode(raw + '==')
        if b[:4] == LUA51_MAGIC:
            return b
    except Exception:
        pass

    return decoded if len(decoded) > 10 else None

def deobf_luraph(source: str) -> dict:
    log      = ['**Obfuscator:** Luraph v15']
    findings = []
    out      = []

    blob = extract_luraph_blob(source)

    if blob:
        log.append(f'✅ Blob extracted — {len(blob)} bytes')

        if blob[:4] == LUA51_MAGIC:
            log.append('✅ Valid Lua 5.1 bytecode header')
            try:
                root = parse_lua51(blob)
                if root:
                    log.append('✅ Bytecode parsed successfully')

                    str_hits = []
                    collect_strings(root, str_hits)
                    log.append(f'✅ {len(str_hits)} string constants recovered')
                    for depth, s in str_hits[:30]:
                        findings.append(f'{"  "*depth}str: `{s[:80]}`')

                    nums = []
                    def collect_nums(p):
                        nums.extend(p.numbers)
                        for c in p.protos: collect_nums(c)
                    collect_nums(root)
                    if nums:
                        log.append(f'✅ {len(nums)} number constants')
                        findings.append(f'nums: {nums[:20]}')

                    skeleton = reconstruct_from_proto(root)
                    out.append('-- ══ LURAPH V15 BYTECODE SKELETON ══')
                    out.append('-- (structural reconstruction — not full source)')
                    out.append(skeleton)

                else:
                    log.append('⚠️  Proto parse returned None')
            except Exception as e:
                log.append(f'⚠️  Parse error: {e}')
                raw_strings = re.findall(
                    b'[\x20-\x7E]{4,}',
                    blob
                )
                for s in raw_strings:
                    try:
                        findings.append(f'raw: `{s.decode()}`')
                    except Exception:
                        pass
                log.append(f'✅ Fallback: {len(raw_strings)} printable strings from blob')

        else:
            log.append('⚠️  Blob present but no Lua5.1 magic — dumping strings')
            raw_strings = re.findall(b'[\x20-\x7E]{4,}', blob)
            for s in raw_strings[:40]:
                try:
                    findings.append(f'`{s.decode()}`')
                except Exception:
                    pass

    else:
        log.append('⚠️  Could not extract bytecode blob')
        log.append('    Falling back to source-level analysis')

    wrapper = _source_passes(source)
    if wrapper.strip():
        out.append('\n-- ══ VM WRAPPER (source passes) ══')
        out.append(wrapper)

    combined = '\n'.join(out) if out else '-- deobf produced no output'

    if findings:
        log.append('\n**🔑 Recovered values:**')
        log.extend(findings[:25])

    return {'source': combined, 'log': '\n'.join(log)}

WL_KEYWORDS = [
    'key','license','hwid','whitelist','valid','expire','auth','token',
    'checkkey','verify','blacklist','discord','webhook','guild','member',
    'role','api','http','request','response','json','post','get',
]

WL_ANNOTATIONS = {
    r'(?:syn\.)?request\s*\(\s*\{':               '--[[ HTTP REQUEST ]]',
    r'(?:Url|url)\s*=\s*"https?://':              '--[[ API ENDPOINT ]]',
    r'(?:key|license|hwid)\s*==':                 '--[[ KEY VALIDATION ]]',
    r'os\.time\s*\(\s*\)|os\.clock':              '--[[ EXPIRY CHECK ]]',
    r'game:GetService\s*\(\s*"HttpService"\s*\)': '--[[ HTTP SERVICE ]]',
    r'LocalPlayer\.UserId':                       '--[[ HWID/USERID ]]',
    r'tostring\s*\(game\.PlaceId\)':              '--[[ PLACE ID ]]',
}

LUA_BUILTINS = {
    'and','break','do','else','elseif','end','false','for','function',
    'goto','if','in','local','nil','not','or','repeat','return','then',
    'true','until','while','print','tostring','tonumber','type','pairs',
    'ipairs','next','select','table','string','math','io','os','bit32',
    'pcall','xpcall','error','assert','require','load','loadstring',
    'request','game','workspace','script','wait','spawn','delay',
    'rawget','rawset','getmetatable','setmetatable','_G','_ENV',
}

def _hex_pass(src: str) -> Tuple[str, list]:
    found = []
    def decode(m):
        raw = m.group(0).strip('"\'')
        try:
            b = bytes(int(h, 16)
                      for h in re.findall(r'[0-9a-fA-F]{2}',
                                          raw.replace('\\x','')))
            dec = b.decode('utf-8', errors='replace')
            if any(k in dec.lower() for k in WL_KEYWORDS):
                found.append(f'hex→ `{dec}`')
            return f'"{dec}"'
        except Exception:
            return m.group(0)
    return re.sub(r'["\'](?:\\x[0-9a-fA-F]{2})+["\']', decode, src), found

def _b64_pass(src: str) -> Tuple[str, list]:
    found = []
    def decode(m):
        try:
            dec = base64.b64decode(m.group(1)+'==').decode('utf-8', errors='replace')
            if dec.isprintable() and len(dec) > 3:
                if any(k in dec.lower() for k in WL_KEYWORDS):
                    found.append(f'b64→ `{dec}`')
                return f'"{dec}"'
        except Exception:
            pass
        return m.group(0)
    return re.sub(r'"([A-Za-z0-9+/]{20,}={0,2})"', decode, src), found

def _xor_pass(src: str) -> Tuple[str, list]:
    found = []
    def try_arr(m):
        try:
            nums  = list(map(int, re.findall(r'\d+', m.group(1))))
            plain = bytes(n & 0xFF for n in nums if 0 < n < 256)
            dec   = plain.decode('utf-8', errors='replace')
            if dec.isprintable() and len(dec) > 3:
                if any(k in dec.lower() for k in WL_KEYWORDS):
                    found.append(f'arr→ `{dec}`')
                return f'"{dec}" --[[decoded]]'
        except Exception:
            pass
        return m.group(0)
    src = re.sub(r'\{((?:\s*\d+\s*,?\s*){5,})\}', try_arr, src)

    def fold_xor(m):
        try:
            val = int(m.group(1), 0)
            key = int(m.group(2), 0)
            r   = val ^ key
            if 0x20 <= r < 0x7F:
                return f'{r} --[["{chr(r)}"]]'
        except Exception:
            pass
        return m.group(0)
    src = re.sub(
        r'bit32\.bxor\s*\(\s*(0x[\da-fA-F]+|\d+)\s*,\s*(0x[\da-fA-F]+|\d+)\s*\)',
        fold_xor, src
    )
    return src, found

def _fold_pass(src: str) -> str:
    def fold(m):
        expr = m.group(0)
        try:
            if re.fullmatch(r'[\d\s\+\-\*\/\%\(\)xXa-fA-F]+', expr):
                result = eval(compile(expr,'<s>','eval'))
                if isinstance(result,(int,float)) and abs(result)<1e12:
                    return str(int(result))
        except Exception:
            pass
        return expr
    return re.sub(
        r'\b(?:0x[\da-fA-F]+|\d+)(?:\s*[\+\-\*\/\%]\s*(?:0x[\da-fA-F]+|\d+)){1,6}\b',
        fold, src
    )

def _strip_pass(src: str) -> str:
    src = re.sub(r'local\s+_\w*\s*=\s*(?:nil|0|false|"")\s*\n', '', src)
    src = re.sub(r'if\s+false\s+then.*?end\s*\n', '', src, flags=re.DOTALL)
    src = re.sub(r'\bdo\s+end\b\s*\n?', '', src)
    src = re.sub(r'\n{3,}', '\n\n', src)
    return src

def _annotate_pass(src: str) -> str:
    for pat, label in WL_ANNOTATIONS.items():
        src = re.sub(f'({pat})',
                     lambda m, lbl=label: f'{lbl}\n{m.group(0)}',
                     src, flags=re.IGNORECASE)
    return src

def _rename_pass(src: str) -> str:
    def is_obf(n):
        if n in LUA_BUILTINS or not n: return False
        if len(n) == 1 and n.isalpha(): return True
        if re.fullmatch(r'[lI]{3,}', n): return True
        if re.fullmatch(r'[O0]{3,}', n): return True
        if re.fullmatch(r'[a-z]\d{2,}', n): return True
        return False
    counts: dict = {}
    for m in re.finditer(r'\b([a-zA-Z_]\w*)\b', src):
        n = m.group(1)
        if is_obf(n): counts[n] = counts.get(n, 0) + 1
    ranked = sorted(counts, key=lambda x: -counts[x])
    rmap   = {old: f'_v{i+1}' for i, old in enumerate(ranked)}
    return re.sub(r'\b([a-zA-Z_]\w*)\b',
                  lambda m: rmap.get(m.group(1), m.group(1)), src)

def _extract_load_payload(src: str) -> str:
    m = re.search(
        r'load(?:string)?\s*\(\s*(?:"((?:[^"\\]|\\.)*)"|\'((?:[^\'\\]|\\.)*)\')' ,
        src, re.DOTALL
    )
    if not m:
        return ''
    raw = m.group(1) or m.group(2)
    try:
        return base64.b64decode(raw+'==').decode('utf-8', errors='replace')
    except Exception:
        return raw

def _source_passes(src: str) -> str:
    src, _ = _hex_pass(src)
    src, _ = _b64_pass(src)
    src, _ = _xor_pass(src)
    src    = _fold_pass(src)
    src    = _strip_pass(src)
    src    = _annotate_pass(src)
    src    = _rename_pass(src)
    src    = re.sub(r'\n{3,}', '\n\n', src)
    return src.strip()

def deobf_luarmor(source: str) -> dict:
    log      = ['**Obfuscator:** Luarmor']
    findings = []

    src, h = _hex_pass(source);  findings += h;  log.append('✅ P1 hex decode')
    src, b = _b64_pass(src);     findings += b;  log.append('✅ P2 b64 decode')
    src, x = _xor_pass(src);     findings += x;  log.append('✅ P3 xor recovery')
    src    = _fold_pass(src);                     log.append('✅ P4 constant fold')

    payload = _extract_load_payload(src)
    if payload:
        log.append('✅ P5 load() payload extracted')
    else:
        log.append('⬜ P5 no load() payload')

    src = _strip_pass(src);     log.append('✅ P6 dead code strip')
    src = _annotate_pass(src);  log.append('✅ P7 WL annotations')
    src = _rename_pass(src);    log.append('✅ P8 var rename')
    src = re.sub(r'\n{3,}', '\n\n', src).strip()

    if payload:
        src += '\n\n-- ══ EXTRACTED LOAD() PAYLOAD ══\n' + payload

    kw = [k for k in WL_KEYWORDS if re.search(rf'\b{k}\b', src, re.I)]
    if kw:
        log.append(f'\n**WL keywords:** `{"`, `".join(kw[:12])}`')

    if findings:
        log.append('\n**🔑 Recovered strings:**')
        log.extend(findings[:20])

    return {'source': src, 'log': '\n'.join(log)}

def deobf_generic(source: str) -> dict:
    src = _source_passes(source)
    return {
        'source': src,
        'log':    '**Obfuscator:** Unknown — ran source-level passes only'
    }

def deobfuscate(source: str) -> dict:
    kind, score = identify(source)
    if kind == ObfType.LURAPH_V15:
        result = deobf_luraph(source)
    elif kind == ObfType.LUARMOR:
        result = deobf_luarmor(source)
    else:
        result = deobf_generic(source)
    result['kind']  = kind.name
    result['score'] = score
    return result

intents = discord.Intents.default()
intents.message_content = True
bot  = commands.Bot(command_prefix=PREFIX, intents=intents)
tree = bot.tree

MAX_INLINE = 1800

def strip_fence(text: str) -> str:
    text = re.sub(r'^```(?:lua)?\s*', '', text.strip())
    return re.sub(r'\s*```$', '', text).strip()

async def fetch_url(url: str) -> Optional[str]:
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(url, timeout=aiohttp.ClientTimeout(total=12)) as r:
                return await r.text()
    except Exception:
        return None

def build_embed(result: dict) -> discord.Embed:
    color_map = {
        'LURAPH_V15': 0x3498db,
        'LUARMOR':    0x9b59b6,
        'GENERIC':    0xe67e22,
        'UNKNOWN':    0x95a5a6,
    }
    color = color_map.get(result.get('kind','UNKNOWN'), 0x95a5a6)
    e = discord.Embed(
        title=f"🔓 Deobfuscator — {result.get('kind','?')} "
              f"(confidence {result.get('score',0)}%)",
        color=color,
    )
    log = result.get('log','')
    e.add_field(name='Pass Log', value=log[:1020], inline=False)
    e.set_footer(text='luraph-v15 + luarmor deobf')
    return e

@bot.event
async def on_ready():
    await tree.sync()
    print(f'[+] {bot.user} ready — Luraph v15 + Luarmor')

@tree.command(name='deobf', description='Deobfuscate Luraph v15 or Luarmor script')
@app_commands.describe(
    code='Paste Lua code or a code block',
    url='Raw URL to fetch the script from',
)
async def slash_deobf(
    interaction: discord.Interaction,
    code: Optional[str] = None,
    url:  Optional[str] = None,
):
    await interaction.response.defer(thinking=True)
    source = None

    if interaction.message:
        for att in interaction.message.attachments:
            if att.filename.endswith(('.lua','.txt')):
                source = (await att.read()).decode('utf-8', errors='replace')
                break

    if not source and url:
        source = await fetch_url(url)
        if not source:
            await interaction.followup.send('❌ Could not fetch URL.')
            return

    if not source and code:
        source = strip_fence(code)

    if not source:
        await interaction.followup.send(
            'Provide input via:\n'
            '`/deobf code:<paste>`\n'
            '`/deobf url:<raw url>`\n'
            'Or attach a `.lua` file.'
        )
        return

    result = deobfuscate(source)
    embed  = build_embed(result)
    out    = result['source']

    if len(out) <= MAX_INLINE:
        await interaction.followup.send(
            embed=embed, content=f'```lua\n{out[:1900]}\n```'
        )
    else:
        buf = io.BytesIO(out.encode())
        await interaction.followup.send(
            embed=embed,
            file=discord.File(buf, 'deobf_output.lua')
        )

@bot.command(name='deobf')
async def prefix_deobf(ctx: commands.Context, *, code: str = ''):
    source = None
    for att in ctx.message.attachments:
        if att.filename.endswith(('.lua','.txt')):
            source = (await att.read()).decode('utf-8', errors='replace')
            break
    if not source and code:
        source = strip_fence(code)
    if not source:
        await ctx.reply('Paste code or attach a `.lua` file.')
        return

    async with ctx.typing():
        result = deobfuscate(source)
        embed  = build_embed(result)
        out    = result['source']
        if len(out) <= MAX_INLINE:
            await ctx.reply(embed=embed, content=f'```lua\n{out[:1900]}\n```')
        else:
            buf = io.BytesIO(out.encode())
            await ctx.reply(embed=embed, file=discord.File(buf,'deobf_output.lua'))

if __name__ == '__main__':
    bot.run(TOKEN)
