# Verification scope

The original JSP-000404 problem is still incomplete. Verification below concerns
only the declared partial results and the completion-contract equivalence.

The source was built with Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`; dependencies remain pinned in
`project/lake-manifest.json`. The local publication build reused the previously
built dependency cache. New modules were compiled and checked separately.

Run from the repository root, after `cd project && lake build`:

```sh
python3 verification/check_axioms.py
python3 experiments/check_four_centers.py
python3 experiments/check_triangle_domination_countermodel.py
python3 experiments/check_capacity_reduction.py
```

The current declared-target audit checks 71 distinct declarations and rejects
axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
`verification/current-axioms.json` and the corresponding `current-*.log` files
record the actual outputs. The new model/counterexample build is in
`verification/general-model-build.log`; scoped official kernel replay is in
`verification/general-model-kernel.log`. This is not an independently
implemented external checker and not a fresh replay of all transitive Mathlib
modules.

GitHub CI installs the pinned toolchain on Ubuntu, builds the project, runs the
listed module kernel checks and theorem audits, and checks the exact diagnostic
scripts. See the run for the exact commit being reviewed; a prior green run does
not certify a later commit. CI success is not an official prize review.

The older four-center checkpoint is described in
`VERIFICATION_FOUR_CENTERS.md`; the earlier eight-target notes are preserved in
`verification/historical-eight-target-checkpoint.md` with their historical scope.

No source here proves the two sharp infinite geometric lower-bound families or
all six completion obligations. No full original-problem verification,
independent mathematical reviewer, accepted priority claim, or award is asserted.
