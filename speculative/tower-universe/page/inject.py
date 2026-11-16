"""Writes page/data.json (from offline.py) into the inline DATA of ../gravastar-tower.html."""
import json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
data = json.load(open(os.path.join(HERE, 'data.json')))
out = [{"delta": r["delta"], "collapse": r["collapse"], "good": r["good"], "pivots": r["pivots"],
        "lam": [[k, float(f"{l:.6e}")] for k, l in r["lam"]]} for r in data]
js = json.dumps(out, separators=(',', ':'))
p = os.path.join(HERE, '..', 'gravastar-tower.html')
html, n = re.subn(r'^const DATA = .*;$', lambda m: 'const DATA = ' + js + ';', open(p).read(), flags=re.M)
assert n == 1, n
open(p, 'w').write(html)
print('injected', len(js), 'bytes;', [(r['delta'], r['collapse'], r['good'], len(r['lam'])) for r in out])
