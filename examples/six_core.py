"""Verify the rise and fall example in Section 3 using only Python's standard library."""

from fractions import Fraction
from functools import cache
from itertools import combinations


vertices = "012345"
pairs = ["".join(p) for p in combinations(vertices, 2)]
blocks = ["".join(q) for k in range(2, 7) for q in combinations(vertices, k)]
inside = {q: [p for p in pairs if set(p) <= set(q)] for q in blocks}
bits = {p: 1 << i for i, p in enumerate(pairs)}
mask = {q: sum(bits[p] for p in inside[q]) for q in blocks}
half = Fraction(1, 2)
stages = [
    (None, {"12345": 1}, {"15": 2, "24": 3}, (10, 10)),
    ("01", dict.fromkeys(["0125", "0145", "1234", "2345"], half),
     {"15": 3, "24": 2, "34": 1}, (11, 10)),
    ("03", {"012345": 1},
     {**dict.fromkeys(["12", "14", "23", "25", "34", "45"], half),
      "15": 2, "24": 1}, (11, 11)),
]


def integral_optimum(score):
    positive = [q for q in blocks if score[q] > 0]

    @cache
    def optimum(available):
        return max((score[q] + optimum(available ^ mask[q]) for q in positive
                    if available & mask[q] == mask[q]), default=0)

    return optimum((1 << len(pairs)) - 1)


residual = set("05 12 14 15 23 24 25 34 45".split())
hosts = {p: set(p) for p in pairs if p not in residual}
for lost, weights, prices, expected in stages:
    if lost:
        hosts[lost].remove("0")
        residual.add(lost)
    required = set(pairs) - residual
    assert all(hosts[p] == set(p) for p in required)
    assert all(not any(set(e) <= row for e in residual) for row in hosts.values())
    score = {q: 2 * len(residual.intersection(inside[q])) - len(inside[q]) - 1
             for q in blocks}
    assert all(x >= 0 for x in (*weights.values(), *prices.values()))
    assert all(sum(x for q, x in weights.items() if e in inside[q]) <= 1 for e in pairs)
    assert all(sum(prices.get(e, 0) for e in inside[q]) >= score[q] for q in blocks)
    fractional = sum(x * score[q] for q, x in weights.items())
    assert fractional == sum(prices.values())
    if lost == "01":
        tight = [q for q in blocks if sum(prices.get(e, 0) for e in inside[q]) == score[q]]
        at34 = [q for q in tight if "34" in inside[q]]
        at15 = [q for q in tight if "15" in inside[q]]
        assert set(at34) == {"1234", "2345"}
        assert set(at15) == {"0125", "0145", "1245", "01245"}
        assert all(mask[a] & mask[b] for a in at34 for b in at15)
        assert not mask["234"] & mask["0145"] and (score["234"], score["0145"]) == (2, 3)
    integral = integral_optimum(score)
    baseline = len(pairs) + sum(map(len, hosts.values())) - 2 * len(required)
    result = baseline - integral, baseline - fractional
    assert result == expected
    print(f"I={integral}, F={fractional}, cp={result[0]}, cp*={result[1]}")
