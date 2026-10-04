#!/usr/bin/env python3
"""Try to falsify a possible general reduction to a three-center subset.

Exploratory only. The proposed domination property is NOT asserted as a theorem.
A satisfying abstract direction model need not be Euclidean-realizable.
"""
from pathlib import Path
import itertools,json,sys,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'.deps'))
import z3

S=int(sys.argv[1]) if len(sys.argv)>1 else 5
N=int(sys.argv[2]) if len(sys.argv)>2 else 4
solver=z3.Solver();solver.set(timeout=20000)
t=z3.Real('t');solver.add(t>=N,t<N+1)
edge={(i,j):z3.Real(f'd_{i}_{j}') for i,j in itertools.combinations(range(S),2)}
for d in edge.values():solver.add(d>=0,d<t)
for i,j,k in itertools.combinations(range(S),3):
    a,b,c=edge[i,j],edge[i,k],edge[j,k]
    solver.add(z3.Or(z3.And(a<b,b<c,c-a>=1,b-a<=t-1,c-b<=t-1),
                     z3.And(c<b,b<a,a-c>=1,a-b<=t-1,b-c<=t-1)))


def sort_expr(values):
    result=[]
    for x in values:
        for j in range(len(result)):
            a=result[j];result[j]=z3.If(a<=x,a,x);x=z3.If(a<=x,x,a)
        result.append(x)
    return result


def weight(vertices,label):
    result=[]
    for i in vertices:
        directions=sort_expr([edge[min(i,j),max(i,j)] for j in vertices if j!=i])
        gaps=[b-a for a,b in zip(directions,directions[1:])]+[t+directions[0]-directions[-1]]
        fs=[z3.Int(f'f_{label}_{i}_{q}') for q in range(len(gaps))]
        for f,g in zip(fs,gaps):solver.add(f>=0,f<=g,g<f+1)
        ki=z3.Sum([z3.If(f>=2,f-1,0) for f in fs])
        solver.add(ki>=0,ki<=N-1)
        result.append(z3.Sum([z3.If(ki==q,2**q,0) for q in range(N)]))
    return z3.Sum(result)


w=weight(list(range(S)),'all')
triples=list(itertools.combinations(range(S),3))
tw={c:weight(c,''.join(map(str,c))) for c in triples}
for v in tw.values():solver.add(w>v)
start=time.monotonic();status=solver.check()
result={'centers':S,'n':N,'hypothesis_tested':'some triple has capacity at least full-set capacity',
        'counterexample_search_status':str(status),'seconds':time.monotonic()-start,
        'is_lean_proof':False,'hypothesis_proved':False}
if status==z3.sat:
    m=solver.model();result.update({'t':str(m.eval(t)),
      'directions':{f'{i},{j}':str(m.eval(x)) for (i,j),x in edge.items()},
      'full_capacity':str(m.eval(w)),
      'triple_capacities':{str(c):str(m.eval(v)) for c,v in tw.items()}})
elif status==z3.unknown:result['reason']=solver.reason_unknown()
out=Path(__file__).resolve().parent/f'triangle-domination-{S}-{N}.json'
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
