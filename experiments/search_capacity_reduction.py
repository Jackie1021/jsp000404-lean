#!/usr/bin/env python3
"""Try to refute proposed general-capacity reductions in the direction model.

No result of this script is a Lean proof. In particular an abstract satisfying
model need not be Euclidean-realizable, and UNSAT for one size is not induction.
"""
from pathlib import Path
import argparse, itertools, json, sys, time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / '.deps'))
import z3

p=argparse.ArgumentParser()
p.add_argument('--centers',type=int,default=5)
p.add_argument('--n',type=int,default=4)
p.add_argument('--subset-size',type=int,default=4)
p.add_argument('--mode',choices=['subset','deletion','global'],default='subset')
p.add_argument('--half',choices=['lower','upper'],default='upper')
p.add_argument('--timeout-ms',type=int,default=30000)
args=p.parse_args()
S,N=args.centers,args.n
assert S>=3 and N>=2
solver=z3.Solver();solver.set(timeout=args.timeout_ms)
t=z3.Real('t');solver.add(t>=N,t<N+1)
solver.add(t<N+z3.RealVal('1/2') if args.half=='lower' else t>=N+z3.RealVal('1/2'))
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
        # A consequence of nonnegative floors and sum(gaps)=t<N+1.
        solver.add(ki>=0,ki<=N-1)
        result.append(z3.Sum([z3.If(ki==q,2**q,0) for q in range(N)]))
    return z3.Sum(result)

w=weight(tuple(range(S)),'all')
size=S-1 if args.mode=='deletion' else args.subset_size
subweights={}
bound=2**N+(2**(N-2) if args.half=='upper' else 0)
if args.mode=='global':
    solver.add(w>bound)
else:
    assert 2<=size<S
    for c in itertools.combinations(range(S),size):
        subweights[c]=weight(c,'_'.join(map(str,c)))
        solver.add(w>subweights[c])
start=time.monotonic();status=solver.check()
result={'parameters':vars(args),'status':str(status),'seconds':time.monotonic()-start,
        'solver':z3.get_version_string(),'is_lean_proof':False,
        'euclidean_realizability_verified':False,'full_original_problem_solved':False,
        'conjectured_global_bound':bound}
if status==z3.sat:
    m=solver.model();result.update({'t':str(m.eval(t)),
      'directions':{f'{i},{j}':str(m.eval(d)) for (i,j),d in edge.items()},
      'full_capacity':m.eval(w).as_long(),
      'subset_capacities':{','.join(map(str,c)):m.eval(v).as_long() for c,v in subweights.items()}})
elif status==z3.unknown:result['reason']=solver.reason_unknown()
name=f'capacity-{args.mode}-{S}-{N}-{args.half}-{size}.json'
(Path(__file__).resolve().parent/name).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
