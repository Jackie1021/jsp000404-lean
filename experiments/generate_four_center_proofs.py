#!/usr/bin/env python3
"""Generate ordinary Lean case proofs; Z3 is only a search assistant.

Every terminal branch is a `linarith only [...]` invocation. Lean must prove
every branch itself. No solver result, native evaluator, axiom or admitted
statement is imported into Lean's logical environment.
"""
from pathlib import Path
import itertools
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'.deps'))
import z3

ROOT=Path(__file__).resolve().parents[1]
EDGE=list(itertools.combinations(range(4),2))
NAMES={e:f'd{e[0]}{e[1]}' for e in EDGE}
Z={name:z3.Real(name) for name in ['n','t']+list(NAMES.values())}
n,t=Z['n'],Z['t']
TRIS=list(itertools.combinations(range(4),3))
STARS=[[NAMES[min(i,j),max(i,j)] for j in range(4) if i!=j] for i in range(4)]
COUNTS={'leaves':0,'branches':0,'theorems':0}


def core(ctx, extra=None):
    s=z3.Solver()
    s.set(timeout=10000)
    for name,expr in ctx:s.assert_and_track(expr,z3.Bool(name))
    if extra is not None:s.assert_and_track(extra,z3.Bool('GOAL_NEG'))
    ans=s.check()
    if ans==z3.unsat:return [str(x) for x in s.unsat_core() if str(x)!='GOAL_NEG']
    if ans==z3.unknown:raise RuntimeError(s.reason_unknown())
    return None


def linear_tactic(names):
    return 'linarith only ['+', '.join(names)+']'


def tree(ctx,preds,indent):
    c=core(ctx)
    if c is not None:
        COUNTS['leaves']+=1
        return [' '*indent+linear_tactic(c)]
    if not preds:raise RuntimeError('A supposedly impossible branch is satisfiable')
    name,options=preds[0]
    COUNTS['branches']+=1
    patterns=[]
    for option in options:
        patterns.append(option[0][0] if len(option)==1 else '⟨'+', '.join(x[0] for x in option)+'⟩')
    out=[' '*indent+'rcases '+name+' with '+' | '.join(patterns)]
    for option in options:
        child=tree(ctx+option,preds[1:],indent+2)
        out.append(' '*indent+'· '+child[0].lstrip())
        out+=child[1:]
    return out


def base(branch,orient):
    ctx=[('hn',n>=3),('ht',n<=t),('htop',t<n+(z3.RealVal('1/2') if branch=='lower' else 1))]
    if branch=='upper':ctx.append(('hhalf',t>=n+z3.RealVal('1/2')))
    for name in NAMES.values():ctx.extend([(name+'lo',Z[name]>=0),(name+'hi',Z[name]<t)])
    for (i,j,k),flip in zip(TRIS,orient):
        a,b,c=[Z[NAMES[e]] for e in [(i,j),(i,k),(j,k)]]
        if flip:a,c=c,a
        conditions=[a<b,b<c,c-a>=1,c-b<=t-1,b-a<=t-1] if flip else \
                   [a<b,b<c,c-a>=1,b-a<=t-1,c-b<=t-1]
        ctx.extend([(f'h{i}{j}{k}_{q}',e) for q,e in enumerate(conditions)])
    return ctx


def gap_data(ctx,vertex):
    star=STARS[vertex]
    for perm in itertools.permutations(range(3)):
        a,b,c=[Z[star[x]] for x in perm]
        ca=core(ctx,z3.Not(a<=b));cb=core(ctx,z3.Not(b<=c))
        if ca is not None and cb is not None:
            return perm,[b-a,c-b,t+a-c],ca,cb
    raise RuntimeError('Triangle orders did not order a star')


def predicates(kind,g,name):
    if kind=='High':return (name,[[(name+'a',x>=n)] for x in g])
    result=[[(name+'a',x>=n-1)] for x in g]
    for i,j in itertools.combinations(range(3),2):
        result.append([(name+'a',g[i]>=2),(name+'b',g[j]>=2),(name+'c',g[i]+g[j]>=n)])
    return name,result


def emit_theorem(name,branch,roles):
    out=[f'theorem {name} (n t '+ ' '.join(NAMES.values())+' : ℝ)',
         '    (hn : 3 ≤ n) (ht : n ≤ t)',
         '    (htop : t < n + '+('1/2' if branch=='lower' else '1')+')']
    if branch=='upper':out.append('    (hhalf : n + 1/2 ≤ t)')
    for d in NAMES.values():out.append(f'    (r{d} : 0 ≤ {d} ∧ {d} < t)')
    for i,j,k in TRIS:
        ds=[NAMES[e] for e in [(i,j),(i,k),(j,k)]]
        out.append(f'    (h{i}{j}{k} : TripleCap '+ ' '.join(ds)+' t)')
    for z,(kind,v) in enumerate(roles):out.append(f'    (P{z} : {kind} n (sortedGaps '+ ' '.join(STARS[v])+' t))')
    out.append('    : False := by')
    for d in NAMES.values():out.append(f'  obtain ⟨{d}lo, {d}hi⟩ := r{d}')
    for ix,(i,j,k) in enumerate(TRIS):
        pat='⟨'+', '.join(f'h{i}{j}{k}_{q}' for q in range(5))+'⟩'
        out.append('  '+('all_goals ' if ix else '')+f'rcases h{i}{j}{k} with {pat} | {pat}')
    for orient in itertools.product([0,1],repeat=4):
        ctx=base(branch,orient)
        c=core(ctx)
        if c is not None:
            COUNTS['leaves']+=1
            out.append('  · '+linear_tactic(c))
            continue
        code=[];preds=[]
        for z,(kind,v) in enumerate(roles):
            perm,g,ca,cb=gap_data(ctx,v)
            a,b,c=[STARS[v][i] for i in perm]
            helper='sortedGaps_order_'+''.join(str(i) for i in perm)
            code.append(f'have G{z} := {helper} '+ ' '.join(STARS[v])+f' t (by {linear_tactic(ca)}) (by {linear_tactic(cb)})')
            code.append(f'rw [G{z}] at P{z}')
            code.append(f'simp only [{kind}] at P{z}')
            preds.append(predicates(kind,g,f'P{z}'))
        code+=tree(ctx,preds,0)
        out.append('  · '+code[0])
        out+=['    '+x for x in code[1:]]
    out.append(f'#print axioms {name}')
    COUNTS['theorems']+=1
    return '\n'.join(out)


def helpers():
    p=ROOT/'project/FourCenterDefs.lean'
    src=p.read_text()
    src=src[:src.index('theorem sortedGaps_order_012')]
    for perm in itertools.permutations(range(3)):
        a,b,c=['abc'[i] for i in perm]
        src+=f'''theorem sortedGaps_order_{''.join(str(i) for i in perm)} (a b c t : ℝ)
    (h0 : {a} ≤ {b}) (h1 : {b} ≤ {c}) :
    sortedGaps a b c t = ({b}-{a},{c}-{b},t+{a}-{c}) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

'''
    src+='end JSP404.FourCenter\n'
    p.write_text(src)


if __name__=='__main__':
    helpers()
    header='''import FourCenterDefs

/-! Generated exhaustive case proofs for the four-center direction relaxation.
Z3 selected linear contradiction cores; every inference below is independently
constructed by Lean's linarith tactic and checked by the Lean kernel.
This is a restricted intermediate result, not the full original problem. -/
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace JSP404.FourCenter

'''
    chunks=[]
    for i,j in itertools.combinations(range(4),2):
        chunks.append(emit_theorem(f'lower_no_two_high_{i}{j}','lower',[('High',i),('High',j)]))
    for i in range(4):
        for j,k in itertools.combinations([v for v in range(4) if v!=i],2):
            chunks.append(emit_theorem(f'lower_no_high_middle_middle_{i}{j}{k}','lower',[('High',i),('Middle',j),('Middle',k)]))
    for i,j in itertools.combinations(range(4),2):
        for k in range(4):
            if k not in [i,j]:
                chunks.append(emit_theorem(f'upper_no_high_high_middle_{i}{j}{k}','upper',[('High',i),('High',j),('Middle',k)]))
    (ROOT/'project/FourCenterExclusions.lean').write_text(header+'\n\n'.join(chunks)+'\n\nend JSP404.FourCenter\n')
    (ROOT/'experiments/four-center-proof-generation.json').write_text(json.dumps(COUNTS,indent=2)+'\n')
    print(json.dumps(COUNTS),flush=True)
