# Four-center capacity bounds in the direction model

**Proved scope:** exactly four centers in the explicit direction relaxation,
every integer n >= 3, and both half-period intervals. **Not proved:** the full
Erdős 504 problem, an arbitrary number of centers, or a Lean bridge from all
Euclidean generalized configurations to this model.

## Statement

Normalize the minimum permitted deviation from a straight angle to 1, so the
unoriented angular period is t. The intended geometric normalization is
t = pi/(pi-A), where A is the angle cap. Four vertices ordered by a generic
projection have six forward unoriented direction parameters in [0,t).

For each ordered triple i<j<k, the long-edge direction lies strictly between the
other two directions. Their total spread is at least 1, and each of the other
two angle differences is at most t-1. `TripleCap` explicitly records these five
inequalities and their reverse-order alternative. `DirectionModel` requires all
four triple constraints and all six direction ranges.

At vertex i, sort its three incident unoriented directions and let g_i1,g_i2,g_i3
be the cyclic gaps, whose sum is t. Put

    k_i = sum_j max(floor(g_ij)-1,0),
    W = sum_i 2^(k_i).

`CapacityData` records the integer floors by both inequalities
f_ij <= g_ij < f_ij+1; it does not assume any desired capacity conclusion.

The checked root theorems are:

1. `capacity_bound_lower`: n <= t < n+1/2 implies W <= 2^n.
2. `capacity_bound_upper`: n+1/2 <= t < n+1 implies W <= 2^n+2^(n-2).

Both quantify over every integer n>=3, every direction model satisfying the
displayed constraints, and every compatible floor certificate. The results are
not an enumeration of a finite range of n.

## Proof structure

The three floors at a vertex sum to at most n. Consequently k_i<=n-1.
If k_i=n-1, one cyclic gap is at least n. If k_i>=n-2, either one gap is at least
n-1, or two gaps are each at least 2 and together at least n.

Exhaustive linear reasoning in the four triple orientations then excludes:

- In the lower half-period, two maximum exponents; also one maximum exponent
  together with two distinct other exponents at least n-2.
- In the upper half-period, two maximum exponents together with a third exponent
  at least n-2.

There are 30 indexed exclusion lemmas. Their generator produced 2,136 terminal
linear contradictions. Every branch is checked by ordinary Lean `linarith` and
the kernel. The generator used Z3 to select linear contradiction cores; no Z3
answer is imported as a Lean axiom or native decision result.

Finally, elementary power-of-two bounds turn these exclusions into the two
claimed bounds for W. See `FourCenterWeights.lean` and `FourCenterBound.lean`.

## A nonvacuous sharp instance

For n=3 and t=15/4, the six rational directions

    d01=23/10, d02=12/5, d03=7/4,
    d12=29/8, d13=6/5, d23=11/10

satisfy the model. Their exponent profile is (2,0,0,2), hence W=10.
`witness_weight_ten` and `witness_attains_upper_capacity` use precisely the same
definitions as the root bounds. This shows the upper bound 10 is attained in
the relaxation and rules out the smaller value 9 there. Exact Euclidean
realizability of these particular rational-angle parameters is not asserted.
The separate earlier ten-point construction remains described in
`FOUR_CENTER_NOTE.md`.

## Why this does not finish the general case

Controlling every four-center restriction is not sufficient by itself to bound
the weight of a larger set. For example, five abstract weights of size 4 have
total 20, although every four of them have sum 16. Extra geometric structure is
needed to pass from local restrictions to a global bound.

An attempted stronger reduction—some three-center subset always has capacity
at least that of the whole set—also fails in the direction relaxation. An exact
five-center model at t=105/22 has total capacity 18, while all ten three-center
subsets have capacity at most 16. The Fraction-only script
`check_triangle_domination_countermodel.py` independently checks this model.
This is not a counterexample to the final classification (the proposed bound
there is 20), and Euclidean realizability is not established. It blocks using
that reduction on the relaxed constraints alone.

The remaining task is a valid general bound that accounts for all centers,
possibly using geometric information absent from this relaxation, followed by
the full geometric bridges and the previously identified remaining obligations.
No new-prize eligibility or first-discovery priority is claimed for this work.
