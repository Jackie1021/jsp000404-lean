# Arbitrary-center model and a deletion obstruction

**Status: partial research. Neither sharp lower-bound family nor the full
original problem is proved.** These results do not establish award eligibility.

## A model for arbitrary cardinality

`GlobalDirections.Model s t` has a forward direction for each ordered pair of
vertices in `Fin s`, with values in `[0,t)` and the same `TripleCap` conditions
used by the four-center model. Unlike the earlier structure, its cardinality is
not fixed at four. A bridge from all original Euclidean configurations remains
a separate obligation.

The checked theorem `GlobalDirections.cardinality_bound` proves

    t <= k  ==>  s <= 2^k, for every natural k,

for every such model. It derives separation of consecutive edge directions from
the triangle conditions, partitions directions into unit bands and injects the
vertices into k-bit strings using the incoming-band indicators. This is the
classical binary-band method, not a claimed new mathematical result; related
prior formalizations in PR 300 informed the investigation.

For noninteger t this permits k=ceil(t), which is too weak for the desired
Sendov bounds. In particular this theorem alone does not prove L1 or L2.

## Why capacity-preserving deletion does not work

`FiniteReductionCounterexample.lean` constructs a model with five vertices and
t=7/2. In units of 1/24 its ten forward directions are

| Edge | Direction units |
|---|---:|
| 01 | 58 |
| 02 | 33 |
| 03 | 69 |
| 04 | 46 |
| 12 | 32 |
| 13 | 82 |
| 14 | 34 |
| 23 | 83 |
| 24 | 81 |
| 34 | 21 |

The period is 84 units. At each vertex, sort the incident directions, form the
successive differences and the wrapping gap, and let

    exponent = sum(max(floor(gap/24)-1, 0)),
    capacity = sum(2^exponent).

The Lean development checks every triangle/range condition and proves that
integer division by 24 computes the required real floor. It uses the same
explicit gap computation for the full list and each deletion, without hardcoding
the asserted capacities into the capacity definition.

- Full exponent profile: `(1,0,1,1,0)`; total capacity **8**.
- Deleting any one of the five vertices gives capacity **7**.
- The vertices are distinct, and the arithmetic proofs use ordinary kernel
  reduction (`decide +kernel`), not `native_decide` or an imported Z3 assertion.

Thus a universal one-vertex deletion preserving capacity is false in this
relaxation. For a five-center set, its four-center subsets are exactly these
deletions, so selecting four centers need not preserve capacity either.

This does **not** refute the final bound, which is 10 at t=7/2. No Euclidean
realizability assertion is made for the rational direction matrix.

An additional exact-rational diagnostic at t=67/14 has full capacity 17 and all
four-center capacities at most 16. That second diagnostic is checked by the
Fraction-only script, not separately formalized in Lean.

## Search results and their limits

`search_capacity_reduction.py` records the actual solver outcome and parameters.
Z3 is optional search tooling and is not trusted by the Lean proofs.

- Five centers, n=4, upper half: search for a violation of the final capacity
  bound returned UNSAT. This fixed-size search is not a formal proof or induction.
- Six centers, n=4, both half intervals: the 45-second searches timed out and
  returned UNKNOWN. They support no mathematical conclusion.
- The two displayed SAT witnesses passed independent rational arithmetic checks
  in `check_capacity_reduction.py`; the n=3 witness also has the Lean proof above.

## What must change in the general proof strategy

The four-center theorem cannot be promoted to all centers by the rejected
deletion rule. A valid sharp argument must use additional structure, a different
induction, or direct global weighted counting. The new arbitrary-center
definitions provide a common setting for that investigation; the classical
cardinality bound is a verified baseline, not the desired sharp result.

All six completion obligations in `CompletionContract.lean` remain unsupplied
as a complete package. No numerical success probability or prize promise is
supported by this checkpoint.
