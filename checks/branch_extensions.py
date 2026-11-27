"""Finite checks of the coefficient-period criterion using polynomial quotient fields."""

from collections import Counter

from phase_dichotomy import Field


def graph_values(field, s, table):
    m = len(table)
    return [0] + [
        field.mul(table[field.power(x, (field.q - 1) // m)], field.power(x, s))
        for x in range(1, field.q)
    ]


def singular_counts(field, s, n, coefficients):
    """Count actual nonzero kernel vectors, then compare to the norm criterion."""
    q = field.q
    assert s**n == q
    norm = [field.power(a, (q - 1) // (s - 1)) for a in range(q)]
    singular = [0] * q
    for c in coefficients:
        assert field.power(c, s) == c
        counts = [0] * q
        for x in range(1, q):
            # The slope is forced by c*x**s = a*x.
            a = field.mul(c, field.power(x, s - 1))
            counts[a] += 1
        target = field.power(c, n)
        for a in range(1, q):
            expected = norm[a] == target
            assert counts[a] == (s - 1 if expected else 0)
            singular[a] += expected
    return Counter(singular[1:])


def two_pieces_on_one_field():
    field = Field(7, [3, 1, 0, 5, 0, 0])
    q = field.q
    multiplier = 2  # Order three in the prime field, and a square there.
    assert field.power(multiplier, 3) == 1 and multiplier != 1
    table = {1: 1, field.negative[1]: multiplier}
    for s, n in [(7**2, 3), (7**3, 2)]:
        values = graph_values(field, s, table)
        assert len(set(values)) == q
        result = singular_counts(field, s, n, table.values())
        expected = ((q-1) // (s-1)) if n % 3 == 0 else 0
        assert result[2] == expected
        if not expected:
            assert result[1] == 2 * ((q-1) // (s-1))
        print(f"F_{q}, base {s}, n={n}: permutation; "
              f"{result[2]} simultaneous singular slopes among {q-1}")


def repeated_coefficients():
    field = Field(5, [2, 0, 1])
    s, n, m, q = 5, 3, 4, field.q
    # The first two labels are interchanged. Labels 3 and 4 share coefficient 1.
    table = {1: 3, 2: 2, 3: 1, 4: 1}
    coefficients = sorted(set(table.values()))
    values = graph_values(field, s, table)
    assert len(set(values)) == q
    counts = singular_counts(field, s, n, coefficients)
    assert counts == {1: 93, 0: 31}
    cases = 0
    for a in field.powers[:4]:  # one of each nonzero slope norm
        ax = [field.mul(a, x) for x in range(q)]
        inverse = field.power(a, q-2)
        images = {field.add(y, field.negative[z]) for y, z in zip(values, ax)}
        operators, fibres = {}, {}
        for c in coefficients:
            operator = []
            preimages = [[] for _ in range(q)]
            for x in range(q):
                y = field.add(field.mul(c, field.power(x, s)), field.negative[ax[x]])
                operator.append(field.mul(inverse, y))
                preimages[y].append(x)
            operators[c], fibres[c] = operator, preimages
        for t in range(q):
            complements = {}
            for c in coefficients:
                y = t
                for other in coefficients:
                    if other != c:
                        y = operators[other][y]
                complements[c] = y
            first = coefficients[0]
            b = ax[operators[first][complements[first]]]
            for alpha in range(q):
                target = field.add(b, alpha)
                reached = False
                for c in coefficients:
                    xs = {field.add(complements[c], u) for u in fibres[c][alpha]}
                    assert xs == set(fibres[c][target])
                    if any(x == 0 or table[field.power(x, (q-1)//m)] == c for x in xs):
                        reached = True
                assert reached == (target in images)
                cases += 1
    print(f"F_{q}: four labels, three coefficients, {cases} intercept-fibre checks")


if __name__ == "__main__":
    repeated_coefficients()
    two_pieces_on_one_field()
