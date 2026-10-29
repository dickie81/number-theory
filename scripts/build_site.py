#!/usr/bin/env python3
"""Build the papers' web site in `_site/`: each compiled paper as `<name>.pdf`, its supplement, if it has one, as
`<name>-supplement.pdf`, and an index page that lists each paper with its date and links to the paper, its supplement
and its source.

Usage: build_site.py [OUT]   (default `_site`)

Run after compiling every `papers/<name>/main.tex` and `papers/<name>/supplement.tex`, as `.github/workflows/pages.yml`
does. A paper without a `main.pdf`, or with a `supplement.tex` but no `supplement.pdf`, is an error, so a failed compile
cannot publish a site that silently lacks it.
"""
import html
import os
import re
import shutil
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = "https://github.com/dickie81/number-theory"


def field_of(tex, command):
    """The argument of the paper's `\\<command>{...}`, with line breaks, math delimiters and spacing commands
    removed."""
    m = re.search(r"\\" + command + r"\{((?:[^{}]|\{[^{}]*\})*)\}", tex)
    if not m:
        return None
    t = m.group(1)
    t = re.sub(r"\\\\", " ", t)
    t = re.sub(r"\$([^$]*)\$", r"\1", t)
    t = re.sub(r"\\[,;:! ]|~", " ", t)
    return " ".join(t.split())


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "_site")
    papers_dir = os.path.join(ROOT, "papers")
    papers = []
    for name in sorted(os.listdir(papers_dir)):
        tex = os.path.join(papers_dir, name, "main.tex")
        if not os.path.isfile(tex):
            continue
        pdf = os.path.join(papers_dir, name, "main.pdf")
        if not os.path.isfile(pdf):
            print(f"build_site: {name}/main.pdf is missing; compile the papers first", file=sys.stderr)
            return 1
        supp = None
        if os.path.isfile(os.path.join(papers_dir, name, "supplement.tex")):
            supp = os.path.join(papers_dir, name, "supplement.pdf")
            if not os.path.isfile(supp):
                print(f"build_site: {name}/supplement.pdf is missing; compile the supplements first", file=sys.stderr)
                return 1
        source = open(tex, encoding="utf-8").read()
        papers.append((name, field_of(source, "title") or name, field_of(source, "date"), pdf, supp))
    os.makedirs(out, exist_ok=True)
    items = []
    for name, title, date, pdf, supp in papers:
        shutil.copyfile(pdf, os.path.join(out, f"{name}.pdf"))
        links = [f'      <li><a href="{name}.pdf">The paper</a> (PDF)</li>']
        if supp:
            shutil.copyfile(supp, os.path.join(out, f"{name}-supplement.pdf"))
            links.append(f'      <li><a href="{name}-supplement.pdf">Its supplement</a> (PDF)</li>')
        links.append(f'      <li><a href="{REPO}/tree/main/papers/{name}">The source</a>, with the paper\'s README</li>')
        when = f'\n    <p class="muted">{html.escape(date)}</p>' if date else ""
        items.append(f'''  <section>
    <h3><a href="{name}.pdf">{html.escape(title)}</a></h3>{when}
    <ul>
{chr(10).join(links)}
    </ul>
  </section>''')
    page = f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>number-theory</title>
  <style>
    :root {{ --bg: #fdfdfd; --fg: #222; --accent: #1a5276; --muted: #555; }}
    @media (prefers-color-scheme: dark) {{
      :root {{ --bg: #1a1a2e; --fg: #e0e0e0; --accent: #7fb3d8; --muted: #aaa; }}
    }}
    body {{ font-family: Georgia, 'Times New Roman', serif; background: var(--bg); color: var(--fg);
           max-width: 46rem; margin: 3rem auto; padding: 0 1rem; line-height: 1.55; }}
    a {{ color: var(--accent); }}
    p.muted {{ color: var(--muted); }}
    h3 {{ margin-bottom: 0.2rem; line-height: 1.3; }}
    h3 + p.muted {{ margin-top: 0; }}
    li {{ margin: 0.3rem 0; }}
  </style>
</head>
<body>
  <h1>number-theory</h1>
  <p>Papers in number theory whose results are checked by the Lean 4 kernel. Each paper claims only its own steps;
  the results it uses from the literature are proved in the library too, and documented in
  <a href="{REPO}/blob/main/formalisations/README.md">formalisations/</a>.</p>
  <h2>Papers</h2>
{chr(10).join(items)}
  <p class="muted">Built from <a href="{REPO}">{REPO.removeprefix("https://")}</a> on every push to
  <code>main</code>.</p>
</body>
</html>
"""
    with open(os.path.join(out, "index.html"), "w", encoding="utf-8") as fh:
        fh.write(page)
    print(f"build_site: {len(papers)} paper(s) in {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
