#!/usr/bin/env python3
"""Build the code font used by the page: a subset of JuliaMono, renamed.

JuliaMono (https://github.com/cormullion/juliamono) is licensed under the SIL Open
Font License 1.1 with the Reserved Font Name "JuliaMono". A subset is a modified
version, so the output is renamed "YieldSpace Mono". The licence is in OFL.txt.

Usage:
  python3 site/fonts/make_mono.py /path/to/juliamono/webfonts

The character set is ASCII plus every non-ASCII character in the Lean sources and the
page source, so re-run this if new symbols appear in the listings. Requires fontTools
and brotli (pip install fonttools brotli).
"""

import sys
from pathlib import Path

from fontTools import subset
from fontTools.ttLib import TTFont

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FAMILY = "YieldSpace Mono"
FACES = {
    "JuliaMono-Regular.woff2": ("Regular", "yieldspace-mono-regular.woff2"),
    "JuliaMono-RegularItalic.woff2": ("Italic", "yieldspace-mono-italic.woff2"),
    "JuliaMono-SemiBold.woff2": ("SemiBold", "yieldspace-mono-semibold.woff2"),
}


def charset():
    chars = {chr(c) for c in range(0x20, 0x7F)} | {"…"}
    for path in list((ROOT / "YieldSpace").glob("*.lean")) + [ROOT / "site" / "src" / "page.html"]:
        chars |= {c for c in path.read_text() if ord(c) > 0x7F}
    return "".join(sorted(chars))


def rename(font, style):
    full = f"{FAMILY} {style}"
    ps = f"{FAMILY.replace(' ', '')}-{style}"
    names = {1: FAMILY, 2: "Italic" if style == "Italic" else "Regular", 3: ps, 4: full, 6: ps,
             16: FAMILY, 17: style}
    table = font["name"]
    for rec in list(table.names):
        if rec.nameID in names or rec.nameID in (21, 22):
            table.removeNames(nameID=rec.nameID)
    for nid, value in names.items():
        table.setName(value, nid, 3, 1, 0x409)


def main(src_dir):
    text = charset()
    for src, (style, out) in FACES.items():
        font = TTFont(Path(src_dir) / src)
        opts = subset.Options()
        opts.flavor = "woff2"
        opts.layout_features = ["*"]
        opts.name_IDs = ["*"]
        sub = subset.Subsetter(opts)
        sub.populate(text=text)
        sub.subset(font)
        rename(font, style)
        font.flavor = "woff2"
        font.save(HERE / out)
        print(f"{out}: {(HERE / out).stat().st_size // 1024} KB")


if __name__ == "__main__":
    main(sys.argv[1])
