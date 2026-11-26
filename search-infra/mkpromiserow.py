#!/usr/bin/env python3
"""One command: (n, m, M, s) -> a ready row file proving the n x m mask M needs
more than s gates to represent, via PromiseGen.rep_lower_mask.
Usage: mkpromiserow.py n m M s out.lean NAMESPACE [--seg H] [--seed K] [--work DIR]
Runs genpromise.py, CaDiCaL (--unsat, LRAT), genpromiserow.py."""
import os, subprocess, sys
a = sys.argv[1:]
def opt(nm, d):
    if nm in a:
        i = a.index(nm); v = a[i + 1]; del a[i:i + 2]; return v
    return d
seg = opt('--seg', '60000'); seed = opt('--seed', '2'); work = opt('--work', '.cache/lrat-promise')
n, m, M, s, out, ns = a
here = os.path.dirname(os.path.abspath(__file__))
cadical = os.path.join(os.path.dirname(here), 'bin', 'cadical')
os.makedirs(work, exist_ok=True)
cnf = os.path.join(work, f'promise_{n}_{m}_{M}_{s}.cnf')
lrat = os.path.join(work, f'promise_{n}_{m}_{M}_{s}.lrat')
subprocess.run([sys.executable, os.path.join(here, 'genpromise.py'), n, m, M, s, cnf],
               check=True)
res = subprocess.run([cadical, '-q', '--unsat', f'--seed={seed}', '--lrat', '--no-binary',
                      cnf, lrat], capture_output=True, text=True)
if res.returncode != 20:
    sys.exit(f'not UNSAT (cadical exit {res.returncode}): no row')
subprocess.run([sys.executable, os.path.join(here, 'genpromiserow.py'), cnf, lrat, out,
                ns, n, m, M, s, '--seg', seg], check=True)
