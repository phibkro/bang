#!/usr/bin/env python3
# tool: role=gen couples=ROADMAP.md,CONTEXT.md,CHANGELOG.md,_site/index.html runs-in=manual
"""Generate _site/index.html — the operator's glanceable progress dashboard (GitHub Pages).

A GENERATED VIEW over data the repo already owns (single-source-of-truth, generate rung):
  • GitHub MILESTONES (`gh api`)      — the PROJECT map (one milestone per product checkpoint)
  • ROADMAP.md  ◊1–◊6 table            — the PROOF map (verification spine)
  • CONTEXT.md  generated proof-state  — the HEALTH panel (headlines clean/flagged · sorries)
  • CHANGELOG.md  ### Features          — the PULSE feed (recent shipped increments)

Self-contained: inline CSS + inline JS only, NO external CDN/font/script — renders offline,
same constraint as an HTML email. FAIL-LOUD like tools/gen-reference.py: if any source's
expected shape is missing, `sys.exit` rather than emit a half-empty dashboard.

Usage:  gen-dashboard.py            write _site/index.html
"""
import html
import json
import re
import shutil
import subprocess
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROADMAP = ROOT / "ROADMAP.md"
CONTEXT = ROOT / "CONTEXT.md"
CHANGELOG = ROOT / "CHANGELOG.md"
SITE = ROOT / "_site"
OUT = SITE / "index.html"
PWA_ASSETS = ROOT / "tools/pwa"  # committed icon rasters, copied verbatim into _site/

# Served at a project-Pages SUBPATH (https://phibkro.github.io/bang/), NOT a root domain.
# So every PWA path — manifest start_url/scope/icons, SW registration scope, cached URLs —
# is RELATIVE ("." / "icon-192.png"), never root-absolute ("/…" would hit the domain root, 404).
THEME_COLOR = "#0d1117"       # matches --bg; tints the installed-app status bar / address bar
BACKGROUND_COLOR = "#0d1117"  # splash-screen background
ICONS = [  # (filename in tools/pwa AND _site, sizes, extra manifest keys)
    ("icon-192.png", "192x192", {}),
    ("icon-512.png", "512x512", {}),
    ("icon-512-maskable.png", "512x512", {"purpose": "maskable"}),
]
CACHE_VERSION = "bang-progress-v1"  # bump to invalidate the precached shell on the next install


def fetch_milestones():
    """GitHub milestones (all states) via `gh api`. {owner}/{repo} resolve from the git remote
    locally and from GITHUB_REPOSITORY in the Action. FAIL-LOUD if gh errors or returns nothing."""
    try:
        raw = subprocess.run(
            ["gh", "api", "repos/{owner}/{repo}/milestones?state=all&per_page=100"],
            capture_output=True, text=True, check=True,
        ).stdout
    except FileNotFoundError:
        sys.exit("gen-dashboard: `gh` not found — needed to fetch milestones (the project map).")
    except subprocess.CalledProcessError as e:
        sys.exit(f"gen-dashboard: `gh api milestones` failed — {e.stderr.strip()}")
    try:
        ms = json.loads(raw)
    except json.JSONDecodeError:
        sys.exit("gen-dashboard: milestones response was not JSON.")
    if not isinstance(ms, list) or not ms:
        sys.exit("gen-dashboard: zero milestones — the project map is the spine of the dashboard.")
    # GitHub returns milestones newest-first; a milestone NUMBER is its creation order = the DAG order.
    ms.sort(key=lambda m: m["number"])
    return ms


def parse_checkpoints(text):
    """(id, name, done) for each `| ◊N | **Name** … | … |` row of the ◊ table in ROADMAP.md.

    done ⟺ the row carries a ✓ (gate-met / DONE / LANDED); ◊6 (Release) has none → pending."""
    rows = []
    for line in text.splitlines():
        s = line.strip()
        if not re.match(r"\|\s*◊[\d.]+\s*\|", s):
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        cid = cells[0]
        nm = re.search(r"\*\*(.+?)\*\*", cells[1])
        name = nm.group(1) if nm else cells[1]
        rows.append((cid, name, "✓" in s))
    if not rows:
        sys.exit("gen-dashboard: no ◊ checkpoint rows in ROADMAP.md — the proof map is keyed off them.")
    return rows


def parse_health(text):
    """(clean, pending, flagged, sorries) from CONTEXT.md's generated proof-state block."""
    m = re.search(
        r"\*\*headlines:\*\*\s*(\d+)\s*clean.*?·\s*(\d+)\s*pending.*?·\s*(\d+)\s*flagged",
        text,
    )
    if not m:
        sys.exit("gen-dashboard: could not parse the proof-state 'headlines:' line in CONTEXT.md.")
    sm = re.search(r"\*\*sorries:\*\*\s*(\d+)", text)
    if not sm:
        sys.exit("gen-dashboard: could not parse the proof-state 'sorries:' line in CONTEXT.md.")
    return int(m.group(1)), int(m.group(2)), int(m.group(3)), int(sm.group(1))


def parse_pulse(text, n=8):
    """(scope, summary, sha) for the most-recent n `### Features` entries (newest first).

    The changelog is append-ordered (generated from conventional commits), so the LAST entries
    are the newest shipped increments — the Linear-pulse analog."""
    feats = re.search(r"### Features\n(.*?)(?:\n### |\n<!--|\Z)", text, re.S)
    if not feats:
        sys.exit("gen-dashboard: no '### Features' section in CHANGELOG.md — the pulse feed is keyed off it.")
    rows = []
    for line in feats.group(1).splitlines():
        cm = re.match(r"-\s*\*\*(.+?)\*\*\s*—\s*(.+?)\s*\(`([0-9a-f]{6,})`\)\s*$", line.strip())
        if cm:
            rows.append((cm.group(1), cm.group(2), cm.group(3)))
    if not rows:
        sys.exit("gen-dashboard: '### Features' parsed to zero entries — the entry shape changed.")
    return list(reversed(rows))[:n]


# ── rendering ──

def e(s):
    return html.escape(str(s))


def milestone_cards(ms):
    # closed = done; the FIRST open milestone with issues = current; the rest = locked.
    current_number = None
    for m in ms:
        if m["state"] == "open" and m["open_issues"] > 0:
            current_number = m["number"]
            break
    cards = []
    for m in ms:
        if m["state"] == "closed":
            cls, badge = "done", "✓"
        elif m["number"] == current_number:
            cls, badge = "current", "▸"
        else:
            cls, badge = "locked", "○"
        oi = m["open_issues"]
        issues = f'{oi} open issue{"s" if oi != 1 else ""}' if oi else (
            "complete" if m["state"] == "closed" else "no issues yet")
        cards.append(
            f'<div class="card {cls}">'
            f'<div class="badge">{badge}</div>'
            f'<div class="ctitle">{e(m["title"])}</div>'
            f'<div class="cdesc">{e(m["description"] or "")}</div>'
            f'<div class="cmeta">{e(issues)}</div>'
            f"</div>"
        )
    return "\n".join(cards)


def checkpoint_pips(cps):
    pips = []
    for cid, name, done in cps:
        cls = "done" if done else "pending"
        icon = "✓" if done else "◇"
        pips.append(
            f'<div class="pip {cls}" title="{e(name)}">'
            f'<div class="picon">{icon}</div>'
            f'<div class="pid">{e(cid)}</div>'
            f'<div class="pname">{e(name)}</div>'
            f"</div>"
        )
    return "\n".join(pips)


def pulse_rows(pulse):
    out = []
    for scope, summary, sha in pulse:
        out.append(
            f'<li><span class="scope">{e(scope)}</span>'
            f'<span class="summary">{e(summary)}</span>'
            f'<span class="sha">{e(sha)}</span></li>'
        )
    return "\n".join(out)


def render(ms, cps, health, pulse):
    clean, pending, flagged, sorries = health
    done_ms = sum(1 for m in ms if m["state"] == "closed")
    done_cp = sum(1 for _, _, d in cps if d)
    return f"""<!DOCTYPE html>
<!-- generated by tools/gen-dashboard.py — do not hand-edit. Run `just dashboard` to regenerate. -->
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="theme-color" content="{THEME_COLOR}">
<link rel="manifest" href="manifest.webmanifest">
<link rel="apple-touch-icon" href="icon-192.png">
<title>bang — progress</title>
<style>
  :root {{
    --bg:#0d1117; --panel:#161b22; --panel2:#1c2230; --edge:#30363d;
    --fg:#e6edf3; --muted:#8b949e; --dim:#6e7681;
    --done:#3fb950; --current:#e3b341; --locked:#484f58;
    --accent:#58a6ff; --amberbg:#2d2410; --greenbg:#0f2417;
    --mono:ui-monospace,"SF Mono",Menlo,Consolas,monospace;
    --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;
  }}
  * {{ box-sizing:border-box; }}
  body {{
    margin:0; background:var(--bg); color:var(--fg);
    font-family:var(--sans); line-height:1.5; padding:2rem 1.5rem 4rem;
  }}
  .wrap {{ max-width:1100px; margin:0 auto; }}
  header {{ display:flex; align-items:baseline; gap:.75rem; flex-wrap:wrap; margin-bottom:.25rem; }}
  h1 {{ font-family:var(--mono); font-size:2rem; margin:0; letter-spacing:-.5px; }}
  h1 .bang {{ color:var(--current); }}
  .tag {{ color:var(--muted); font-size:.95rem; }}
  .updated {{ color:var(--dim); font-size:.8rem; margin-bottom:2rem; }}
  section {{ margin-bottom:2.5rem; }}
  h2 {{
    font-size:.8rem; text-transform:uppercase; letter-spacing:.12em;
    color:var(--muted); font-weight:600; margin:0 0 1rem;
    border-bottom:1px solid var(--edge); padding-bottom:.5rem;
    display:flex; justify-content:space-between; align-items:center;
  }}
  h2 .count {{ color:var(--dim); font-weight:500; letter-spacing:normal; text-transform:none; }}

  /* project cards */
  .cards {{ display:grid; grid-template-columns:repeat(auto-fill,minmax(240px,1fr)); gap:1rem; }}
  .card {{
    background:var(--panel); border:1px solid var(--edge); border-radius:10px;
    padding:1rem; position:relative; overflow:hidden;
  }}
  .card::before {{ content:""; position:absolute; left:0; top:0; bottom:0; width:4px; }}
  .card.done::before {{ background:var(--done); }}
  .card.current::before {{ background:var(--current); }}
  .card.locked::before {{ background:var(--locked); }}
  .card.current {{ background:linear-gradient(135deg,var(--amberbg),var(--panel)); border-color:#5c4a1a; }}
  .card.locked {{ opacity:.62; }}
  .badge {{
    position:absolute; top:.7rem; right:.8rem; font-family:var(--mono);
    font-size:1.1rem; font-weight:700;
  }}
  .card.done .badge {{ color:var(--done); }}
  .card.current .badge {{ color:var(--current); }}
  .card.locked .badge {{ color:var(--locked); }}
  .ctitle {{ font-weight:650; font-size:1.02rem; margin-bottom:.4rem; padding-right:1.5rem; }}
  .cdesc {{ color:var(--muted); font-size:.82rem; line-height:1.45; }}
  .cmeta {{
    margin-top:.7rem; font-family:var(--mono); font-size:.72rem;
    color:var(--dim); text-transform:uppercase; letter-spacing:.04em;
  }}
  .card.current .cmeta {{ color:var(--current); }}

  /* checkpoint pips */
  .track {{ display:flex; gap:.4rem; flex-wrap:wrap; }}
  .pip {{
    flex:1 1 130px; background:var(--panel); border:1px solid var(--edge);
    border-radius:8px; padding:.7rem .6rem; text-align:center;
  }}
  .pip.done {{ background:linear-gradient(180deg,var(--greenbg),var(--panel)); border-color:#1c422c; }}
  .picon {{ font-family:var(--mono); font-size:1.15rem; font-weight:700; }}
  .pip.done .picon {{ color:var(--done); }}
  .pip.pending .picon {{ color:var(--dim); }}
  .pid {{ font-family:var(--mono); font-size:.9rem; color:var(--fg); margin-top:.2rem; }}
  .pname {{ font-size:.72rem; color:var(--muted); margin-top:.15rem; }}

  /* health */
  .health {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(150px,1fr)); gap:1rem; margin-bottom:1rem; }}
  .stat {{ background:var(--panel); border:1px solid var(--edge); border-radius:10px; padding:1rem 1.2rem; }}
  .stat .num {{ font-family:var(--mono); font-size:1.9rem; font-weight:700; line-height:1; }}
  .stat .lbl {{ color:var(--muted); font-size:.78rem; margin-top:.4rem; }}
  .stat.clean .num {{ color:var(--done); }}
  .stat.flagged .num {{ color:var(--current); }}
  .stat.sorries .num {{ color:var(--accent); }}
  .stat.pending .num {{ color:var(--muted); }}
  .bar {{ height:8px; border-radius:4px; background:var(--panel2); overflow:hidden; display:flex; border:1px solid var(--edge); }}
  .bar .seg-clean {{ background:var(--done); }}
  .bar .seg-flagged {{ background:var(--current); }}
  .barlbl {{ display:flex; justify-content:space-between; color:var(--dim); font-size:.72rem; margin-top:.4rem; font-family:var(--mono); }}

  /* pulse */
  ul.pulse {{ list-style:none; margin:0; padding:0; }}
  ul.pulse li {{
    display:flex; align-items:baseline; gap:.7rem; padding:.55rem .2rem;
    border-bottom:1px solid var(--edge); font-size:.9rem;
  }}
  ul.pulse li:last-child {{ border-bottom:none; }}
  .scope {{
    font-family:var(--mono); font-size:.72rem; color:var(--accent);
    background:var(--panel2); border:1px solid var(--edge); border-radius:5px;
    padding:.1rem .4rem; white-space:nowrap; flex:0 0 auto;
  }}
  .summary {{ color:var(--fg); flex:1 1 auto; }}
  .sha {{ font-family:var(--mono); font-size:.72rem; color:var(--dim); flex:0 0 auto; }}

  footer {{ color:var(--dim); font-size:.75rem; text-align:center; margin-top:3rem; font-family:var(--mono); }}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <h1><span class="bang">bang</span> — progress</h1>
    <span class="tag">a verified effect-typed language · paradigm &amp; runtime are values</span>
  </header>
  <div class="updated">generated view · {done_ms}/{len(ms)} projects · {done_cp}/{len(cps)} proof checkpoints · {clean} headlines clean</div>

  <section>
    <h2>Projects <span class="count">the product map — programs that pull features into being</span></h2>
    <div class="cards">
{milestone_cards(ms)}
    </div>
  </section>

  <section>
    <h2>Proof checkpoints <span class="count">the verification spine — ◊1 → ◊6</span></h2>
    <div class="track">
{checkpoint_pips(cps)}
    </div>
  </section>

  <section>
    <h2>Proof health <span class="count">axiom census of the headline theorems</span></h2>
    <div class="health">
      <div class="stat clean"><div class="num">{clean}</div><div class="lbl">headlines clean (⊆ trusted-3)</div></div>
      <div class="stat flagged"><div class="num">{flagged}</div><div class="lbl">flagged (carry sorryAx)</div></div>
      <div class="stat sorries"><div class="num">{sorries}</div><div class="lbl">open sorries (burndown)</div></div>
      <div class="stat pending"><div class="num">{pending}</div><div class="lbl">pending (build in flight)</div></div>
    </div>
    <div class="bar">
      <div class="seg-clean" style="width:{pct(clean, clean + flagged)}%"></div>
      <div class="seg-flagged" style="width:{pct(flagged, clean + flagged)}%"></div>
    </div>
    <div class="barlbl"><span>{clean} clean</span><span>{flagged} flagged</span></div>
  </section>

  <section>
    <h2>Pulse <span class="count">recent shipped increments</span></h2>
    <ul class="pulse">
{pulse_rows(pulse)}
    </ul>
  </section>

  <footer>generated by tools/gen-dashboard.py — do not hand-edit</footer>
</div>
<script>
  // Relative 'sw.js' + scope './' — both resolve under the /bang/ subpath, never the domain root.
  if ('serviceWorker' in navigator) {{
    window.addEventListener('load', function () {{
      navigator.serviceWorker.register('sw.js', {{ scope: './' }}).catch(function () {{}});
    }});
  }}
</script>
</body>
</html>
"""


def pct(part, whole):
    return round(100 * part / whole) if whole else 0


# ── PWA files (make the dashboard installable + instant-open offline) ──

def render_manifest():
    """The web app manifest. All paths RELATIVE to the manifest URL (/bang/…), never root."""
    return json.dumps(
        {
            "name": "bang — progress",
            "short_name": "bang",
            "description": "Live progress tracker for bang — a verified effect-typed language.",
            "display": "standalone",
            "theme_color": THEME_COLOR,
            "background_color": BACKGROUND_COLOR,
            "start_url": ".",
            "scope": ".",
            "icons": [
                {"src": fn, "sizes": sizes, "type": "image/png", **extra}
                for fn, sizes, extra in ICONS
            ],
        },
        indent=2,
        ensure_ascii=False,
    )


def render_sw():
    """Service worker: stale-while-revalidate. Serve the cached shell instantly, refresh in the
    background so the next open converges to the latest CI build. All URLs relative to /bang/."""
    shell = json.dumps(["./"] + [fn for fn, _, _ in ICONS]
                       + ["index.html", "manifest.webmanifest"])
    return f"""// generated by tools/gen-dashboard.py — do not hand-edit.
const CACHE_VERSION = {json.dumps(CACHE_VERSION)};
const SHELL = {shell};

self.addEventListener('install', (event) => {{
  event.waitUntil(
    caches.open(CACHE_VERSION)
      .then((cache) => cache.addAll(SHELL))
      .then(() => self.skipWaiting())
  );
}});

self.addEventListener('activate', (event) => {{
  event.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(
        keys.filter((k) => k !== CACHE_VERSION).map((k) => caches.delete(k))
      ))
      .then(() => self.clients.claim())
  );
}});

// Stale-while-revalidate: reply from cache at once, fetch fresh to update it for next time.
self.addEventListener('fetch', (event) => {{
  if (event.request.method !== 'GET') return;
  event.respondWith(
    caches.open(CACHE_VERSION).then((cache) =>
      cache.match(event.request).then((cached) => {{
        const fresh = fetch(event.request)
          .then((res) => {{
            if (res && res.status === 200 && res.type === 'basic') {{
              cache.put(event.request, res.clone());
            }}
            return res;
          }})
          .catch(() => cached);
        return cached || fresh;
      }})
    )
  );
}});
"""


def write_pwa_files():
    """manifest + sw + icons into _site/. Icons are committed rasters copied verbatim (CI needs
    no rasterizer); re-rasterize from tools/pwa/*.svg with resvg when the glyph changes."""
    (SITE / "manifest.webmanifest").write_text(render_manifest())
    (SITE / "sw.js").write_text(render_sw())
    for fn, _, _ in ICONS:
        src = PWA_ASSETS / fn
        if not src.exists():
            sys.exit(f"gen-dashboard: missing icon {src.relative_to(ROOT)} — "
                     "re-rasterize tools/pwa/*.svg (resvg) before generating.")
        shutil.copyfile(src, SITE / fn)


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    ms = fetch_milestones()
    cps = parse_checkpoints(ROADMAP.read_text())
    health = parse_health(CONTEXT.read_text())
    pulse = parse_pulse(CHANGELOG.read_text())
    SITE.mkdir(parents=True, exist_ok=True)
    OUT.write_text(render(ms, cps, health, pulse))
    write_pwa_files()
    print(
        f"dashboard: wrote {OUT.relative_to(ROOT)} + manifest/sw/{len(ICONS)} icons — "
        f"{len(ms)} milestones · {len(cps)} checkpoints · "
        f"{health[0]} clean/{health[2]} flagged/{health[3]} sorries · {len(pulse)} pulse entries."
    )


if __name__ == "__main__":
    main()
