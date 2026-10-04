# JSP-000404 research development

**Status: incomplete research, not an award submission.** The full original
problem has not been solved by this development. No prize eligibility, priority,
independent verification, or award entitlement is claimed.

**Public research repository:** maintained by [Jackie1021](https://github.com/Jackie1021) with OpenAI Codex assistance. Public commits record research progress, not a completed-proof priority claim.

**2026-10-04 update:** an arbitrary-center direction model and its classical
binary-band cardinality bound are proved in Lean. A five-center model is also
proved to have capacity 8 while every four-center deletion has capacity 7,
blocking capacity-preserving deletion as a general proof route. See
[the exact scope and remaining gap](GENERAL_MODEL_PROGRESS.md).

**Earlier checkpoint:** the four-center direction-model capacity inequalities,
for every integer n >= 3, are now proved in Lean. See
`FOUR_CENTER_RESULT.md` and `VERIFICATION_FOUR_CENTERS.md`. This does not cover
an arbitrary number of centers or supply the full Euclidean correspondence.

## Selected problem and objective

JSP-000404 is Blumenthal's planar extremal-angle problem, also Erdős 504. It is
different from the earlier poster problem 31 / JSP-000327 / Erdős 397.
For each integer N >= 3, determine the supremum of the angles that every set
of N distinct points in the Euclidean plane must determine.

The objective is a complete, unconditional formalization of the full answer.
Existing partial formalizations are prior work. Reconstructing their finite
cases, or publishing these preliminary lemmas, does not establish a claim to a
new award. Mathematical authorship and formalization authorship must be assessed
separately; the Sendov classification must not be presented as our discovery.

Sendov's final 1995 Theorem 4.1 uses

- alpha(N) = pi * (1 - 2/(2m+1)) for 2^m < N <= 2^m + 2^(m-2);
- alpha(N) = pi * (1 - 1/(m+1)) for 2^m + 2^(m-2) < N <= 2^(m+1),

for m >= 2, together with alpha(3)=pi/3 and alpha(4)=pi/2.
The numerator TWO in the first branch follows the final theorem, printed p.42;
the contradictory numerator ONE in some descriptions must not be copied.

## Work done in this development

- `project/Problem.lean`: literal Euclidean-plane definitions, both lower and
  approximate upper requirements, full classification as a proposition, and the
  two infinite lower-bound families. Declaring a proposition does not prove it.
- `project/Reduction.lean`: the proposed lower/upper specification determines
  the supremum; restriction/extension in the number of points; an explicitly
  conditional assembly theorem reducing all intervals to threshold lower bounds
  and endpoint upper constructions.
- `project/Regression.lean`: exact integer certificates for ten explicit points
  and a generalized-direction table. These are algebraic regression statements;
  a complete Lean bridge to generalized Euclidean configurations is not included.
- `experiments/check_four_centers.py`: rational interval arithmetic and integer
  arithmetic for a concrete obstruction to the published four-center induction
  subcase. The analytic identities used by this script are stated explicitly.
- `project/FourCenterBound.lean`: two unconditional capacity bounds inside the
  explicitly defined four-center direction model, for all integer n >= 3.
- `project/FourCenterWitness.lean`: a consistent rational instance whose capacity
  is 10, checked in the same definitions as the capacity bounds.
- `project/FourCenterExclusions.lean`: exhaustive ordinary Lean proofs of the
  forbidden weight patterns; Z3 was used to find contradiction cores, not as a
  trusted proof oracle. The resulting Lean build needs no Z3 installation.

`project/CompletionContract.lean` checks that six outstanding obligations are equivalent to the full target. It supplies none of the six obligations.

The four-center obstruction **does not disprove the final classification**.
It reproduces a type of problem already reported in prior work. It shows why a
claimed induction step cannot be imported unchanged as the main lower proof.

## Remaining mathematical obligations

The principal unresolved tasks are the two families, for every m >= 2:

1. Every 2^m+1 point set determines an angle >= pi*(1-2/(2m+1)).
2. Every 2^m+2^(m-2)+1 point set determines an angle >= pi*(1-1/(m+1)).

Public partial submissions claim cases through N=16. Their source statements
were inspected, but their complete dependencies were not independently rebuilt
in this development. The next thresholds beyond those claimed cases are N=17
and N=21. Solving just those two finite cases would still not solve the original
problem, which quantifies over every N.

Both endpoint upper constructions and the N=3,4 cases also remain to be supplied
in this project. They may be integrated from appropriately licensed, reviewed
prior formalizations with attribution; they are not silently assumed proved.
`classification_of_thresholds` is conditional on these precise obligations.

## Reproduction

Lean: `leanprover/lean4:v4.33.0`.
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Transitive versions are fixed by `project/lake-manifest.json`.

From `project/`, with the pinned toolchain installed:

```sh
lake exe cache get Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Tactic
lake build
lake env lean Audit.lean
lake env lean FourCenterAudit.lean
lake env lean CompletionContract.lean
lake env lean GeneralAudit.lean
```

From this directory:

```sh
python3 experiments/check_four_centers.py
python3 experiments/check_capacity_reduction.py
python3 verification/check_axioms.py
```

See `VERIFICATION_FOUR_CENTERS.md` for the current checks and their limitations.
`VERIFICATION.md` records the earlier eight-target starting checkpoint.
Do not infer verification from these instructions alone.

## Sources and attribution

- [Original Erdős 504 statement](https://www.erdosproblems.com/504).
- B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta
  Mathematica Hungarica 69 (1995), 27–46. Relevant printed pages: 37–40 (Lemma
  4.1), 42 (Theorem 4.1). [Journal volume](https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf).
- [Prior PR 42](https://github.com/TheJustinSunPrize/awards/pull/42): formula
  comparison and partial construction results.
- [Prior PR 100](https://github.com/TheJustinSunPrize/awards/pull/100): exact small
  and dyadic cases.
- [Prior PR 300](https://github.com/TheJustinSunPrize/awards/pull/300): partial
  classification and reported issue in the general capacity argument. Its pinned
  source is `e80d0b209dc60257c1109ee8ea904ea0d7dd5ef4` in CollinYuanjieRen/awards.
- [Prior PR 647](https://github.com/TheJustinSunPrize/awards/pull/647): eleven-point
  lower-bound extension.
- [Current official award process at the inspected revision](https://github.com/TheJustinSunPrize/awards/blob/e9e118d00022d693151d87af0c69d180dc5e5efd/docs/award-process.md).

This development was prepared with OpenAI Codex assistance at the direction of
the user controlling GitHub account Jackie1021. That account name is not a
verified legal name or a final decision about award attribution. No copied
third-party Lean proof is built by this project. Mathematical definitions and
the reduction reflect standard extremal reasoning; the four-center obstruction
is not claimed as a first discovery. Private identity and payment data are not
included. No new award PR or claim has been submitted for this development.
