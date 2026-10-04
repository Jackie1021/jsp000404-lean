#!/usr/bin/env python3
"""Independent exact-arithmetic check of the exploratory five-center model.

Uses Python's Fraction only, not Z3. This validates a countermodel in the
direction relaxation. It does not assert Euclidean realizability.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools,json

root=Path(__file__).resolve().parent
src=json.loads((root/'triangle-domination-5-4.json').read_text())
t=F(src['t'])
d={tuple(map(int,k.split(','))):F(v) for k,v in src['directions'].items()}
assert all(0<=x<t for x in d.values())
for i,j,k in itertools.combinations(range(5),3):
    a,b,c=d[i,j],d[i,k],d[j,k]
    assert ((a<b<c and c-a>=1 and b-a<=t-1 and c-b<=t-1) or
            (c<b<a and a-c>=1 and a-b<=t-1 and b-c<=t-1))


def capacity(vertices):
    profile=[]
    for i in vertices:
        directions=sorted(d[min(i,j),max(i,j)] for j in vertices if j!=i)
        gaps=[b-a for a,b in zip(directions,directions[1:])]+[t+directions[0]-directions[-1]]
        profile.append(sum(max(g.numerator//g.denominator-1,0) for g in gaps))
    return sum(2**k for k in profile),profile


full,profile=capacity(list(range(5)))
triples={str(c):capacity(c)[0] for c in itertools.combinations(range(5),3)}
assert full==18 and max(triples.values())==16
assert full>max(triples.values())
assert full<=2**4+2**(4-2)
result={'status':'exact_rational_checks_passed','full_capacity':full,
        'full_profile':profile,'triple_capacities':triples,
        'counterexample_to_three_center_domination_in_relaxation':True,
        'counterexample_to_final_classification':False,
        'euclidean_realizability_verified':False,'is_lean_proof':False}
(root/'triangle-domination-exact-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
