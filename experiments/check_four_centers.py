#!/usr/bin/env python3
"""Exact rational bounds for the four-center obstruction in Sendov's induction.

Analytic facts used, not formalized here:
  atan(x) = sum (-1)^j x^(2j+1)/(2j+1), 0 < x < 1,
  with alternating-series remainder bounds;
  pi = 16 atan(1/5) - 4 atan(1/239) (Machin's identity).
Everything after those facts uses exact Fraction arithmetic. No floating-point
angle is used to decide an inequality or a floor. This is a regression result,
not a disproof of the final classification and not a complete award submission.
"""
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path


def atan_interval(x, terms=30):
    assert 0 < x < 1 and terms % 2 == 0
    lower = sum(((-1)**j * x**(2*j+1) / (2*j+1) for j in range(terms)), F(0))
    return lower, lower + x**(2*terms+1) / (2*terms+1)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def sub(a, b):
    return a[0]-b[1], a[1]-b[0]


def mul(c, a):
    return (c*a[0], c*a[1]) if c >= 0 else (c*a[1], c*a[0])


def encoded(a):
    return {"lower": str(a[0]), "upper": str(a[1])}


a = atan_interval(F(1, 2))
b = atan_interval(F(3, 5))
pi = sub(mul(16, atan_interval(F(1, 5))), mul(4, atan_interval(F(1, 239))))
halfpi = mul(F(1, 2), pi)
gaps = [
    [a, sub(b, a), sub(pi, b)],
    [sub(pi, b), sub(b, a), a],
    [sub(halfpi, a), sub(halfpi, a), mul(2, a)],
    [sub(halfpi, b), sub(halfpi, b), mul(2, b)],
]
floors = []
gap_evidence = []
for row in gaps:
    fr = []
    for gap in row:
        normalized = F(15, 4)*gap[0]/pi[1], F(15, 4)*gap[1]/pi[0]
        fl = normalized[0].numerator // normalized[0].denominator
        assert fl == normalized[1].numerator // normalized[1].denominator
        fr.append(fl)
        gap_evidence.append(encoded(normalized))
    floors.append(fr)
profile = [sum(max(f-1, 0) for f in row) for row in floors]
assert profile == [2, 2, 0, 0]
weight = sum(2**k for k in profile)
assert weight == 10 > 9

# Every angle determined by the four centers is <= pi - 4*pi/15.
# At the two base vertices the angles are a, b and b-a.
# At the lower apex: pi-2a and pi/2+a; at the upper apex:
# pi-2b and pi/2-b. (Repeated symmetric angles are omitted.)
possible_angles = [a, b, sub(b, a), sub(pi, mul(2, a)),
                   add(halfpi, a), sub(pi, mul(2, b)), sub(halfpi, b)]
cap = mul(F(11, 15), pi)
assert all(x[1] < cap[0] for x in possible_angles)

# A rational upper bound on cos(cap) proves that -2/3 is a stricter bound.
# On [0, pi], cos is decreasing. A Taylor partial sum ending with the
# nonnegative term of even index 30 is an upper bound for cos(cap.lower).
x = cap[0]
term = F(1)
cos_upper = term
for j in range(1, 31):
    term *= -x*x / ((2*j-1)*(2*j))
    cos_upper += term
assert cos_upper < F(-2, 3)

# The hierarchy actually contains the angle pi-atan(1/6)-atan(5/6).
# It exceeds 5*pi/7, keeping its actual t in (7/2,15/4), within the
# very same n=3, delta>=1/2 subcase even though the test cap is strict.
internal_angle = sub(pi, add(atan_interval(F(1, 6)), atan_interval(F(5, 6))))
assert internal_angle[0] > mul(F(5, 7), pi)[1]

# Generalized directions for two four-leaf perfect binary clusters plus
# two singleton centers. Between clusters, directions use the centers;
# within a cluster, they use the first binary level at which leaves differ.
centers_int = [(-10, 0), (10, 0), (0, 5), (0, 6)]


def cluster(i):
    return 0 if i < 4 else 1 if i < 8 else i-6


def generalized_direction(i, j):
    ci, cj = cluster(i), cluster(j)
    if ci != cj:
        return tuple(centers_int[cj][d]-centers_int[ci][d] for d in range(2))
    if i == j:
        return (0, 0)
    high_diff = j % 4 // 2 - i % 4 // 2
    low_diff = j % 2 - i % 2
    v, w = ((1, 6), (-5, 6)) if ci == 0 else ((5, 6), (-1, 6))
    return tuple(high_diff*v[d] if high_diff else low_diff*w[d] for d in range(2))


generalized_checks = 0
for j in range(10):
    for i, k in itertools.combinations([r for r in range(10) if r != j], 2):
        u, v = generalized_direction(j, i), generalized_direction(j, k)
        nu, nv = sum(z*z for z in u), sum(z*z for z in v)
        dot = sum(a*b for a, b in zip(u, v))
        assert nu > 0 and nv > 0
        assert dot >= 0 or 9*dot*dot <= 4*nu*nv
        generalized_checks += 1

# A corresponding ten-point ordinary configuration, checked by integer algebra.
P = []
for center, v, w in [((-1000000, 0), (1, 6), (-5, 6)),
                      ((1000000, 0), (5, 6), (-1, 6))]:
    for s, t in itertools.product([-1, 1], repeat=2):
        P.append(tuple(center[d] + 1000*s*v[d] + t*w[d] for d in range(2)))
P.extend([(0, 500000), (0, 600000)])
assert len(set(P)) == 10
checks = 0
for j in range(10):
    for i, k in itertools.combinations([r for r in range(10) if r != j], 2):
        u = tuple(P[i][d]-P[j][d] for d in range(2))
        v = tuple(P[k][d]-P[j][d] for d in range(2))
        dot = sum(x*y for x, y in zip(u, v))
        nu = sum(x*x for x in u)
        nv = sum(x*x for x in v)
        assert dot >= 0 or 9*dot*dot <= 4*nu*nv
        checks += 1

result = {
    "status": "research_regression_only",
    "centers": [["-1", "0"], ["1", "0"], ["0", "1/2"], ["0", "3/5"]],
    "t": "15/4", "cap": "11*pi/15", "floors": floors,
    "profile": profile, "weight": weight,
    "published_four_center_subcase_maximum": 9,
    "contradicts_final_classification": False,
    "intervals_for_scaled_gaps": gap_evidence,
    "ordinary_points": P, "exact_integer_angle_checks": checks,
    "generalized_angle_checks": generalized_checks,
    "cosine_bound_stricter_than_cap": True,
    "actual_t_in_same_published_subcase": "7/2 < t_actual < 15/4",
    "integer_certificate_bound": "cos(angle) >= -2/3",
    "unformalized_analytic_inputs": ["alternating atan series", "Machin identity",
        "alternating cosine series and monotonicity on [0,pi]",
        "geometric interpretation of generalized directions"],
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
output = Path(__file__).resolve().parent / "four-center-result.json"
output.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({k: result[k] for k in ["status", "profile", "weight",
    "published_four_center_subcase_maximum", "contradicts_final_classification",
    "exact_integer_angle_checks"]}, indent=2))
