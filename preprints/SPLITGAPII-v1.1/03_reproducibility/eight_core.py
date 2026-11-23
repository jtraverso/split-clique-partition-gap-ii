"""Certifica con aritmética entera que el factor de borrado de Split Gap II es 2."""
from functools import cache
from itertools import combinations
from fractions import Fraction


CORE = '01234567'
REQUIRED = frozenset('14 15 17 35 36 46 47 56 57 67'.split())
REMOVED_PAIR = '14'
PAIRS = tuple(''.join(p) for p in combinations(CORE, 2))
PAIR_BIT = {e: 1 << i for i, e in enumerate(PAIRS)}
INSIDE = {
    ''.join(q): frozenset(''.join(p) for p in combinations(q, 2))
    for k in range(2, len(CORE) + 1) for q in combinations(CORE, k)
}
MASK = {q: sum(PAIR_BIT[e] for e in pairs) for q, pairs in INSIDE.items()}

# Las entradas de estos arreglos tienen denominadores 9 y 3, respectivamente.
PACKING_TIMES_9 = {
    **dict.fromkeys('016 037 045 126 237 245 0134 1234'.split(), 4),
    **dict.fromkeys('0256 0257 0267'.split(), 2),
    **dict.fromkeys('134 0126 0237 0245'.split(), 1),
}
DUAL_BEFORE_TIMES_3 = {
    **dict.fromkeys('05 06 07 25 26 27'.split(), 1),
    **dict.fromkeys('16 37 45'.split(), 2),
    **dict.fromkeys('01 03 04 12 23 24'.split(), 3),
    '02': 5,
}
INTEGRAL = '245 237 034 0126'.split()


def check(condition, message):
    if not condition:
        raise SystemExit(f'FAIL: {message}')


def scores(required):
    return {q: len(pairs) - 2 * len(pairs & required) - 1 for q, pairs in INSIDE.items()}


def integral_maximum(score):
    positive = [(MASK[q], w) for q, w in score.items() if w > 0]

    @cache
    def search(available):
        return max(
            (w + search(available ^ mask) for mask, w in positive if available & mask == mask),
            default=0,
        )

    value = search((1 << len(PAIRS)) - 1)
    return value, search.cache_info().currsize


def verify():
    check(len(INSIDE) == 247, 'todos los subconjuntos de al menos dos vértices')
    check(REMOVED_PAIR in REQUIRED and len(REQUIRED) == 10, 'instancia')
    check(all(p in PAIR_BIT for p in REQUIRED | DUAL_BEFORE_TIMES_3.keys()), 'pares válidos')
    check(all(q in INSIDE for q in PACKING_TIMES_9), 'piezas válidas')
    check(all(w >= 0 for w in (*PACKING_TIMES_9.values(), *DUAL_BEFORE_TIMES_3.values())),
          'no negatividad')
    for e in PAIRS:
        load = sum(w for q, w in PACKING_TIMES_9.items() if e in INSIDE[q])
        check(load <= 9, f'capacidad fraccional de {e}')
        if e == REMOVED_PAIR:
            check(load == 9, 'saturación fraccional del par 14')
    check(all(INSIDE[a].isdisjoint(INSIDE[b]) for a, b in combinations(INTEGRAL, 2)),
          'piezas enteras disjuntas')

    differences = []
    for deleted in (False, True):
        required = REQUIRED - {REMOVED_PAIR} if deleted else REQUIRED
        w = scores(required)
        dual = DUAL_BEFORE_TIMES_3.copy()
        if deleted:
            dual[REMOVED_PAIR] = dual.get(REMOVED_PAIR, 0) + 6
        for q, pairs in INSIDE.items():
            check(sum(dual.get(e, 0) for e in pairs) >= 3 * w[q], f'cota dual para {q}')
        frac = Fraction(sum(mult * w[q] for q, mult in PACKING_TIMES_9.items()), 9)
        check(frac == Fraction(sum(dual.values()), 3), 'igualdad primal-dual')
        integer, states = integral_maximum(w)
        check(sum(w[q] for q in INTEGRAL) == integer == 11, 'óptimo entero')
        check(frac == Fraction(41 if deleted else 35, 3), 'óptimo fraccional')

        edge_count = len(PAIRS) + 2 * len(REQUIRED) - int(deleted)
        baseline = edge_count - 2 * len(required)
        gap = frac - integer
        differences.append(gap)
        print(f'Borrado={int(deleted)}: I={integer}, F={frac}, cp={baseline-integer}, '
              f'cp*={baseline-frac}, brecha={gap}; {states} estados enteros')

    check(differences[1] - differences[0] == 2, 'salto de dos con un único borrado')
    print('PASS: el factor universal de estabilidad es exactamente 2.')


if __name__ == '__main__':
    verify()
