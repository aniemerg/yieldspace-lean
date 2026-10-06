#!/usr/bin/env python3
"""Render site/src/social.png, the 1200x630 preview image used for link cards.

Needs Google Chrome (or Chromium). The PNG is committed, so the normal build does not
need this script; re-run it only if the title or Figure 1 changes.

Usage:  python3 site/social_card.py [path-to-chrome]
"""

import subprocess
import sys
import tempfile
from pathlib import Path

import build

CHROME = sys.argv[1] if len(sys.argv) > 1 else (
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
KATEX_FONTS = build.SITE / "node_modules" / "katex" / "dist" / "fonts"

CARD = f"""<!doctype html><html><head><meta charset="utf-8"><style>
@font-face {{ font-family: "KaTeX_Main"; src: url("{(KATEX_FONTS / 'KaTeX_Main-Regular.woff2').as_uri()}"); }}
@font-face {{ font-family: "KaTeX_Main"; font-style: italic;
  src: url("{(KATEX_FONTS / 'KaTeX_Main-Italic.woff2').as_uri()}"); }}
{(build.SITE / 'src' / 'style.css').read_text()}
body {{ margin: 0; width: 1200px; height: 630px; overflow: hidden; }}
.card {{ display: grid; grid-template-columns: 1fr 520px; gap: 40px; align-items: center;
  height: 630px; box-sizing: border-box; padding: 0 64px; }}
h1 {{ font-size: 64px; font-weight: 400; line-height: 1.1; margin: 0 0 24px; }}
p {{ font-size: 28px; line-height: 1.35; color: var(--ink-2); margin: 0; }}
</style></head><body class="ys" data-theme="light"><div class="card">
<div><h1>YieldSpace in Lean</h1>
<p>Eight properties of the constant power sum invariant, proved in Lean 4 and explained</p></div>
<div>{build.fig_curves()}</div></div></body></html>"""


def main():
    with tempfile.TemporaryDirectory() as tmp:
        card = Path(tmp) / "card.html"
        card.write_text(CARD)
        out = build.SITE / "src" / "social.png"
        subprocess.run(
            [CHROME, "--headless=new", "--disable-gpu", "--hide-scrollbars", "--force-device-scale-factor=1",
             "--window-size=1200,630", "--allow-file-access-from-files", "--virtual-time-budget=2000",
             f"--screenshot={out}", card.as_uri()],
            check=True, capture_output=True,
        )
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
