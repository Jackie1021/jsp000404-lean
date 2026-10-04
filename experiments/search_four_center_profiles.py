#!/usr/bin/env python3
"""Research-only SMT relaxation of four-center capacity profiles.

Normalized unoriented edge directions lie in [0,t), with h=1 and pi=t.
For vertices ordered by a generic projection, every triple i<j<k has
theta_ik between theta_ij and theta_jk. The three angle-cap inequalities
are linear. These are necessary conditions; no sufficiency for geometric
realizability is asserted. An SMT result is NOT a Lean theorem.
"""
import itertools
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / '.deps'))
import z3


def model_problem(branch, timeout=45000, n_fixed=None):
    s = z3.Solver()
    s.set(timeout=timeout)
    n = z3.Int('n')
    t = z3.Real('t')
    s.add(n >= 2, t >= n, t < n+1)
    if n_fixed is not None:
        s.add(n == n_fixed)
    s.add(t < n+z3.RealVal('1/2') if branch == 'lower' else t >= n+z3.RealVal('1/2'))
    edges = {(i,j): z3.Real(f'd_{i}{j}') for i,j in itertools.combinations(range(4),2)}
    for d in edges.values():
        s.add(d >= 0, d < t)
    for i,j,k in itertools.combinations(range(4),3):
        x,y,w = edges[i,j],edges[j,k],edges[i,k]
        s.add(z3.Or(z3.And(x < w, w < y, y-x >= 1, w-x <= t-1, y-w <= t-1),
                    z3.And(y < w, w < x, x-y >= 1, x-w <= t-1, w-y <= t-1)))
    powers = []
    floors = []
    for i in range(4):
        a,b,c = [edges[min(i,j),max(i,j)] for j in range(4) if i!=j]
        lo = z3.If(a<b,z3.If(a<c,a,c),z3.If(b<c,b,c))
        hi = z3.If(a>b,z3.If(a>c,a,c),z3.If(b>c,b,c))
        mid = a+b+c-lo-hi
        gap = [mid-lo,hi-mid,t+lo-hi]
        fs = [z3.Int(f'f_{i}{j}') for j in range(3)]
        for f,g in zip(fs,gap):
            s.add(f >= 0, f <= g, g < f+1)
        exponent = z3.Int(f'k_{i}')
        s.add(exponent == z3.Sum([z3.If(f>=2,f-1,0) for f in fs]))
        # Follows from nonnegative floors whose sum is <= n.
        s.add(exponent >= 0, exponent <= n-1)
        powers.append(exponent)
        floors.append(fs)
    high = z3.Sum([z3.If(k == n-1,1,0) for k in powers])
    mid = z3.Sum([z3.If(k >= n-2,1,0) for k in powers])
    if branch == 'lower':
        s.add(z3.Or(high >= 2, z3.And(high >= 1, mid >= 3)))
    else:
        s.add(high >= 2, mid >= 3)
    return s,n,t,edges,powers,floors


def run(branch, n_fixed=None):
    s,n,t,edges,powers,floors=model_problem(branch,n_fixed=n_fixed)
    suffix=branch if n_fixed is None else f'{branch}-n{n_fixed}'
    here=Path(__file__).resolve().parent
    (here/f'four-centers-{suffix}.smt2').write_text(s.to_smt2())
    start=time.monotonic();answer=s.check()
    out={'branch':branch,'fixed_n':n_fixed,'status':str(answer),
         'seconds':time.monotonic()-start,'solver':z3.get_version_string(),
         'is_lean_proof':False,'is_full_problem_solution':False}
    if answer == z3.sat:
        m=s.model()
        out['n']=m.eval(n).as_long();out['t']=str(m.eval(t))
        out['edges']={f'{i}{j}':str(m.eval(x)) for (i,j),x in edges.items()}
        out['powers']=[m.eval(x).as_long() for x in powers]
        out['floors']=[[m.eval(x).as_long() for x in row] for row in floors]
    elif answer == z3.unknown:
        out['reason']=s.reason_unknown()
    (here/f'four-centers-{suffix}-result.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out),flush=True)


if __name__=='__main__':
    run(sys.argv[1] if len(sys.argv)>1 else 'lower',
        int(sys.argv[2]) if len(sys.argv)>2 else None)
