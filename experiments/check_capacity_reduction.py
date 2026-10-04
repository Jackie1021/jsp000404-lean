#!/usr/bin/env python3
"""Check discovered SAT witnesses using Fraction, without importing Z3."""
from fractions import Fraction as F
from pathlib import Path
import itertools,json

here=Path(__file__).resolve().parent
checked=[]
for file in sorted(here.glob('capacity-*.json')):
    data=json.loads(file.read_text())
    if not isinstance(data, dict) or data.get('status')!='sat':
        continue
    par=data['parameters']; s,n=par['centers'],par['n']; t=F(data['t'])
    assert n<=t<n+1
    assert (t<n+F(1,2)) if par['half']=='lower' else (t>=n+F(1,2))
    d={tuple(map(int,k.split(','))):F(v) for k,v in data['directions'].items()}
    assert set(d)==set(itertools.combinations(range(s),2))
    assert all(0<=x<t for x in d.values())
    for i,j,k in itertools.combinations(range(s),3):
        a,b,c=d[i,j],d[i,k],d[j,k]
        assert ((a<b<c and c-a>=1 and b-a<=t-1 and c-b<=t-1) or
                (c<b<a and a-c>=1 and a-b<=t-1 and b-c<=t-1))
    def capacity(vertices):
        ks=[]
        for i in vertices:
            directions=sorted(d[min(i,j),max(i,j)] for j in vertices if i!=j)
            gaps=[b-a for a,b in zip(directions,directions[1:])]+[t+directions[0]-directions[-1]]
            assert all(g>=0 for g in gaps) and sum(gaps)==t
            ks.append(sum(max(g.numerator//g.denominator-1,0) for g in gaps))
        return sum(2**k for k in ks),ks
    full,profile=capacity(range(s)); assert full==data['full_capacity']
    if par['mode']=='global':
        assert full>data['conjectured_global_bound']
        sub={}
    else:
        size=s-1 if par['mode']=='deletion' else par['subset_size']
        sub={','.join(map(str,v)):capacity(v)[0] for v in itertools.combinations(range(s),size)}
        assert sub==data['subset_capacities']
        assert all(full>x for x in sub.values())
    checked.append({'source':file.name,'full_capacity':full,'profile':profile,
                    'subset_capacities':sub,'exact_checks_passed':True,
                    'is_lean_proof':False,'euclidean_realizability_verified':False,
                    'contradicts_final_capacity_bound':full>data['conjectured_global_bound']})
assert checked, 'No satisfying model was checked.'
(here/'capacity-reduction-exact-check.json').write_text(json.dumps(checked,indent=2)+'\n')
print(json.dumps(checked,indent=2))
