> Historical local checkpoint. The current publication build is recorded in `verification/publication-build.log`. These historical checks do not certify a complete solution.

# Development verification — 2026-09-21

**Verdict: partial coverage. The original problem is not fully solved by this
development, and this package is not ready for an award submission.**

This is an author-side development check. It is not an independent human review,
an official prize review, or a verification of the earlier third-party packages.

## Actual mechanical results

- `lake build`: exit 0, 3086 jobs in the dependency/build graph. This count is
  not a count of new mathematical results.
- `lake env lean Audit.lean`: exit 0. Eight explicit theorem targets checked.
- `lake env leanchecker --verbose Problem Reduction Regression`: exit 0.
  All three local modules replayed. This was **not** `--fresh` replay of the
  entire transitive Mathlib dependency graph.
- `python3 experiments/check_four_centers.py`: exit 0. Exact rational interval
  comparisons and 360 integer angle certificates for each of two configurations.

Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` were used.
The Mathlib dependency cache was reused/extended. Cache download failures for
some files were resolved by the subsequent successful source build; no failed
download was treated as a proof result. Raw successful-check logs are in `logs/`.

| Target | Observed axioms | Scope |
| --- | --- | --- |
| `JSP404.exactValue_isLUB` | propext, Classical.choice, Quot.sound | Semantic bridge for the exact-value specification |
| `JSP404.unavoidable_mono` | propext, Classical.choice, Quot.sound | Lower-bound monotonicity |
| `JSP404.approximableCap_mono` | propext, Classical.choice, Quot.sound | Restriction of upper constructions |
| `JSP404.classification_of_thresholds` | propext, Classical.choice, Quot.sound | Conditional assembly; essential hypotheses still unproved |
| `JSP404.Regression.points_distinct` | propext, Classical.choice, Quot.sound | Ten integer points are distinct |
| `JSP404.Regression.all_integer_certificates` | propext | Integer inequalities only |
| `JSP404.Regression.all_generalized_certificates` | propext | Direction-table integer inequalities only |
| `JSP404.Regression.generalized_nonzero` | none | Distinct labels have nonzero generalized direction |

No checked target depends on `sorryAx`, a custom axiom, or native evaluation.
This does not make the conditional assembly theorem unconditional. Its displayed
type in `logs/audit.log` retains all missing mathematical hypotheses.

## Explicit completeness judgments

1. **Does this development address the intended problem?** Yes, as a research
   specification and partial development. It uses distinct points in the literal
   Euclidean plane, all triples, both bounds, every interval, and the corrected
   published constant. An independent human correspondence review is pending.
2. **Did the checked source pass?** The local source files recorded in the
   package's SHA-256 manifest passed the checks listed above. There is no selected
   completed-proof Git commit or public proof submission for this development.
3. **Does it fully solve the original problem?** No. The two infinite lower-bound
   families, complete upper constructions and small base cases are not proved in
   this project. `FullClassification` is a definition of the goal, not a theorem.
4. **Does it meet the prize's complete-Lean-proof requirement?** No. The remaining
   hypotheses prevent an unconditional proof of the original full statement.

The regression's trigonometric interpretation and circle-hierarchy realization
are explained in `FOUR_CENTER_NOTE.md`; their formal Lean bridges are absent.
The Python script states its analytic inputs explicitly. Its exact arithmetic
does not by itself constitute a Lean proof of those analytic inputs.

## Competition and current policy

The official repository was rechecked at
`97205339934220486d221e7ba22124d31a058f48`. Searches for both JSP-000404 and
Erdős 504 returned the known partial submissions. No complete submission was
identified by this search; that is not a global proof of priority or exclusivity.
PR 42 is now closed; its maintainer response explicitly cites partial coverage.

The latest rules add an exception for mathematical solvers already recorded by
the project. That exception does not waive the merged-PR requirement for a Lean
formalization claim and does not make this partial development eligible.
No new PR, claim issue, identity email, or payment request was sent.
