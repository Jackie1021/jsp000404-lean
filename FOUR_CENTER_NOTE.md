# A checked obstruction to an induction subcase

This note is a research diagnostic, not a complete solution of Erdős 504.
Related weight-profile objections were already reported in PR 300. No discovery
priority is claimed for this observation.

Write t = pi/(pi-A), where A is the maximum permitted generalized angle.
The published four-center subcase in Sendov's Lemma 4.1 (printed p.39) states
that, for n=floor(t) and 1/2 <= t-n < 1, the maximum profile is

    (n-1, n-2, n-2, n-3).

For t=15/4 this would have weight 4+2+2+1=9. However, take four centers

    (-1,0), (1,0), (0,1/2), (0,3/5).

Set a=atan(1/2), b=atan(3/5). The cyclic gaps between the *unoriented*
directions from each center to the other three, in radians, are:

| Center | Three gaps |
| --- | --- |
| (-1,0) | a, b-a, pi-b |
| (1,0) | pi-b, b-a, a |
| (0,1/2) | pi/2-a, pi/2-a, 2a |
| (0,3/5) | pi/2-b, pi/2-b, 2b |

The script proves by rational interval enclosure that the floors of
`t*gap/pi` are `(0,0,3)`, `(3,0,0)`, `(1,1,1)`, `(1,1,1)` respectively.
Consequently, the capacities `k_i = sum max(floor(t*gap/pi)-1,0)` are

    (2,2,0,0),

giving weight 10. All the angles between the centers are strictly below
A=11*pi/15. The interval enclosures use the alternating arctangent series and
Machin's identity for pi, with all comparisons performed as rational arithmetic.

For actual generalized-direction realizability, put a perfect binary four-leaf
cluster at each of the first two centers and singleton clusters at the remaining
centers. Use binary-level directions `(1,6),(-5,6)` at the left center and
`(5,6),(-1,6)` at the right center. The associated 10-leaf direction table is
tested on all triples. For each two nonzero arms u,v, the certificate is

    dot(u,v) >= 0, or
    9*dot(u,v)^2 <= 4*normSq(u)*normSq(v).

This implies cos(angle) >= -2/3. A rational Taylor bound verifies that
cos(11*pi/15) < -2/3, so every generalized angle is strictly below A. Small
nested disjoint circles realize the two binary cluster hierarchies. That last
geometric interpretation is a mathematical argument, not a completed Lean
formalization of generalized configurations.

The hierarchy also contains the angle `pi-atan(1/6)-atan(5/6)`, which the
rational intervals show is greater than `5*pi/7`. Thus its actual maximum
angle yields `7/2 < t_actual < 15/4`, in the same `n=3, delta>=1/2` subcase.
Using a strict upper cap does not move the example out of the stated subcase.

The script also supplies a finite-scale ordinary ten-point realization using
integer coordinates and verifies the same certificate on its 360 angles with
unordered arms. The Lean regression module separately checks the integer
certificates and the nonzero generalized directions. Its formal scope is limited
to those algebraic statements; the trigonometric and circle-hierarchy bridges
are explicitly outside that module.

## What follows, and what does not

The stated maximum 9 for this four-center subcase cannot justify the induction.
Nevertheless, the final proposed bound for t=15/4 is 2^3+2^(3-2)=10, so this
configuration is fully compatible with the final classification. It is not a
counterexample to that classification. A replacement general upper bound on
capacity, or a direct proof of the two threshold lower families, is still needed.
