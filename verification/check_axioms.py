#!/usr/bin/env python3
"""Run the declared theorem audits and reject non-standard transitive axioms.

This checks the listed declarations, not original-problem completeness, novelty,
priority or award eligibility. It does not modify the allowed axiom list.
"""
from pathlib import Path
import json,re,subprocess

root=Path(__file__).resolve().parents[1]
allow={'propext','Classical.choice','Quot.sound'}
files=['Audit.lean','FourCenterAudit.lean','CompletionContract.lean','GeneralAudit.lean']
records=[]
for file in files:
    proc=subprocess.run(['lake','env','lean',file],cwd=root/'project',capture_output=True,text=True)
    output=proc.stdout+proc.stderr
    (root/'verification'/('current-'+file+'.log')).write_text(output)
    if proc.returncode:
        raise SystemExit(f'{file}: Lean failed, exit {proc.returncode}')
    matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S)
    if not matches:
        raise SystemExit(f'{file}: no axiom records found')
    for name,block in matches:
        axioms={a.strip() for a in block.split(',') if a.strip()}
        if axioms-allow:
            raise SystemExit(f'{name}: disallowed axioms {sorted(axioms-allow)}')
        records.append({'declaration':name,'axioms':sorted(axioms),'audit_file':file})
result={'status':'listed_declarations_passed','declarations_checked':len(records),
        'standard_axioms_only':True,'complete_original_problem_verified':False,
        'records':records}
(root/'verification'/'current-axioms.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'}))
