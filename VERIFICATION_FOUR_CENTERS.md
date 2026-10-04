> Historical local checkpoint. The current publication build is recorded in `verification/publication-build.log`. These historical checks do not certify a complete solution.

# Four-center development verification

**Overall verdict for JSP-000404: partial coverage. The original problem remains
unsolved by this development. The four-center direction-model component passes
the mechanical checks listed below.**

This is an author-side check, not an independent human or official prize review.

## Checked results

- The complete current local project built successfully with Lean 4.33.0.
- All 54 public theorem declarations in the six new modules passed the explicit
  `#check` and `#print axioms` audit. Each uses only a subset of `propext`,
  `Classical.choice`, and `Quot.sound`.
- The official Lean `leanchecker` replayed `FourCenterDefs`,
  `FourCenterExclusions`, `FourCenterCapacity`, `FourCenterWeights`,
  `FourCenterBound`, and `FourCenterWitness`, exiting 0.
- All nine dependency revisions match `lake-manifest.json`; Mathlib is pinned to
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
- The five-center exploratory countermodel passed an independent exact rational
  arithmetic check without importing Z3. This check is not a Lean theorem and
  does not establish Euclidean realizability.

Kernel replay here is scoped to the six new modules, not a `--fresh` replay of
the entire Mathlib dependency graph. No separately implemented external checker
or independent mathematical reviewer is claimed.

The Lean build does not require Z3. Z3 5.1.0 (Python package 5.1.0.0) was used by
the optional search/generation scripts. The generated proofs contain ordinary
case splits and `linarith`; no solver certificate is accepted as an axiom, and
no checked target depends on `sorryAx` or native evaluation.

## Reproduction

From `project/`, with the pinned Lean toolchain:

```sh
lake build
lake env lean FourCenterAudit.lean
lake env leanchecker --verbose FourCenterDefs FourCenterExclusions FourCenterCapacity FourCenterWeights FourCenterBound FourCenterWitness
```

The last command requires a compatible `leanchecker` executable. The observed
successful run used the executable bundled with the pinned Lean installation.
Raw successful outputs are in `verification/build-v2.log`, `verification/four-center-audit.log`,
and `verification/four-center-kernel-replay.log`.

From the research directory:

```sh
python3 experiments/check_triangle_domination_countermodel.py
```

Optional regeneration/search requires `z3-solver==5.1.0.0` available to Python
(the local scripts also look in `.deps`). Regeneration is not required to check
the shipped Lean source. `four-center-targets.json` lists the audited declarations;
`SHA256-v2.json` identifies the delivered files.

## Completeness judgments

1. **Does this address the original problem?** It proves a relevant restricted
   capacity component. Its direction-model hypotheses are explicit, and the
   formal bridge to the complete Euclidean problem is still absent.
2. **Did the selected source pass verification?** The local source snapshot in
   `SHA256-v2.json` passed the listed mechanical checks. There is no public
   completed-proof repository commit for this development.
3. **Does it fully solve the original problem?** No. An arbitrary number of
   centers and the two original infinite lower-bound families remain unresolved.
   The project also lacks the complete integration of upper constructions and
   small base cases identified in the earlier checkpoint.
4. **Does it meet the prize's full-proof requirement?** No. A correct restricted
   component cannot be submitted as a complete solution.

No new prize PR, award claim, identity email or payment request was sent. This
checkpoint does not establish contribution priority or entitlement to payment.
