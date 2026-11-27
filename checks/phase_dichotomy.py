"""Finite checks for the extension-degree dichotomy, using polynomial quotients.

Run with Python 3. Sets of translates are tested against actual affine lines.
For the shared field of size 5**6, check the proposed quadratic witness and
the image bound in every cubic slope class. No asymptotic claim is enumerated.
"""

from itertools import combinations
from math import gcd


class Field:
    """Base-p digits represent polynomials modulo X**k + sum(coeff[i]*X**i)."""

    def __init__(self, p, coeff):
        self.p = p
        self.q = p ** len(coeff)
        self.weights = [p**i for i in range(len(coeff))]
        self.digits = [tuple(x // w % p for w in self.weights) for x in range(self.q)]
        reductions = [sum((-c * a % p) * w for a, w in zip(coeff, self.weights))
                      for c in range(p)]
        self.powers = []
        self.logs = [-1] * self.q
        x = 1
        for i in range(self.q - 1):
            if x == 0 or self.logs[x] != -1:
                raise ArithmeticError("The given generator misses nonzero residues")
            self.powers.append(x)
            self.logs[x] = i
            x = self.add(x * p % self.q, reductions[self.digits[x][-1]])
        if x != 1:
            raise ArithmeticError("The generator did not close its orbit")
        self.negative = [sum((-c % p) * w for c, w in zip(row, self.weights))
                         for row in self.digits]

    def add(self, x, y):
        return sum(((c + d) % self.p) * w
                   for c, d, w in zip(self.digits[x], self.digits[y], self.weights))

    def mul(self, x, y):
        if x == 0 or y == 0:
            return 0
        return self.powers[(self.logs[x] + self.logs[y]) % (self.q - 1)]

    def power(self, x, k):
        if x == 0:
            return int(k == 0)
        return self.powers[(self.logs[x] * k) % (self.q - 1)]


def square_model(p):
    # X**2 + X + 2 is primitive for both p = 3 and p = 5.
    field = Field(p, [2, 1])
    q = field.q
    degree = p + (q - 1) // 2
    graph = [field.power(x, degree) for x in range(q)]
    hits = [0] * q
    for slope in range(q):
        for x, y in enumerate(graph):
            intercept = field.add(y, field.negative[field.mul(slope, x)])
            for shift in range(q):
                b = field.add(intercept, field.negative[shift])
                hits[shift] |= 1 << (q * slope + b)
    full = (1 << (q*q)) - 1

    def covers(shifts):
        seen = 0
        for shift in shifts:
            seen |= hits[shift]
        return seen == full

    def anchored_count(size):
        return sum(covers((0,) + rest) for rest in combinations(range(1, q), size - 1))

    # Translate a nonempty solution to contain zero. Any smaller solution can
    # be extended to size p-1. Also check each proposed optimal line directly.
    smaller = anchored_count(p - 1)
    optimal = anchored_count(p)
    lines = {tuple(sorted(field.mul(c, v) for c in range(p))) for v in range(1, q)}
    if smaller != 0 or optimal == 0 or len(lines) != p + 1 or not all(map(covers, lines)):
        raise ArithmeticError((p, smaller, optimal))
    print(f"F_{q}: B({q},{degree})={p}; anchored counts {smaller}/{optimal} "
          f"at sizes {p-1}/{p}; all {len(lines)} base-field lines cover")


def branch_criterion(field, s, n, m=2):
    """Count nonzero kernel vectors directly for every slope and branch."""
    q = field.q
    if s**n != q or (s-1) % m:
        raise ValueError("Incompatible subfield")
    norm = [field.power(x, (q-1) // (s-1)) for x in range(q)]
    singular = [0] * q
    for sign in field.powers[::(q-1)//m]:
        counts = [0] * q
        for x in range(1, q):
            slope = field.mul(sign, field.power(x, s-1))
            counts[slope] += 1
        sign_norm = field.power(sign, n)
        for slope in range(1, q):
            expected = norm[slope] == sign_norm
            if counts[slope] != (s-1 if expected else 0):
                raise ArithmeticError(("kernel", s, n, slope, sign))
            singular[slope] += expected
    return singular


def degenerate_transport(field, slopes, shifts, parameters, s=3, m=2):
    """Compare every candidate from the common variable with actual fibres."""
    q = field.q
    signs = field.powers[::(q-1)//m]
    graph = [field.power(x, s + (q-1)//m) for x in range(q)]
    cases = 0
    for a in slopes:
        ax = [field.mul(a, x) for x in range(q)]
        inverse = field.power(a, q-2)
        direct = {field.add(y, field.negative[z]) for y, z in zip(graph, ax)}
        branches = []
        fibres = []
        for sign in signs:
            linear = [field.add(field.mul(sign, field.power(x, s)), field.negative[ax[x]])
                      for x in range(q)]
            branch = [field.mul(inverse, y) for y in linear]  # U_sign = L_sign/a.
            preimages = {}
            for x, y in enumerate(linear):
                preimages.setdefault(y, []).append(x)
            branches.append(branch)
            fibres.append(preimages)
        for t in parameters:
            # Evaluate the complementary products Q_j and the full product P.
            other = []
            for j in range(m):
                y = t
                for i, branch in enumerate(branches):
                    if i != j:
                        y = branch[y]
                other.append(y)
            b = ax[branches[0][other[0]]]
            for alpha in shifts:
                target = field.add(b, alpha)
                reached = False
                for j, sign in enumerate(signs):
                    candidates = {field.add(other[j], c)
                                  for c in fibres[j].get(alpha, ())}
                    if candidates != set(fibres[j].get(target, ())):
                        raise ArithmeticError(("candidate fibre", q, a, alpha, t, sign))
                    if any(x == 0 or field.power(x, (q-1)//m) == sign for x in candidates):
                        reached = True
                if reached != (target in direct):
                    raise ArithmeticError(("monomial image", q, a, alpha, t))
                cases += 1
    return cases


def odd_cubic_base():
    # The exceptional family s=m+1=3 has a singular branch at every slope.
    for n, coeff in ((3, [1, 2, 0]), (9, [1, 0, 1, 2, 0, 0, 0, 0, 0])):
        field = Field(3, coeff)
        q = field.q
        if any(count != 1 for count in branch_criterion(field, 3, n)[1:]):
            raise ArithmeticError(("missing singular branch", n))
        if n == 3:
            slopes, shifts, parameters = range(1, q), range(q), range(q)
        else:
            # Two slopes of opposite norm, in the large-degree proof range.
            slopes = (1, field.powers[1])
            shifts = parameters = (0, 1, 2, field.powers[1], field.powers[5], field.powers[25])
        cases = degenerate_transport(field, slopes, shifts, parameters)
        print(f"F_{q}: unique singular branch at all {q-1} nonzero slopes; "
              f"{cases} common-variable fibre checks")


def shared_field():
    field = Field(5, [2, 1, 0, 0, 0, 0])
    q = field.q
    for s, n in ((125, 2), (25, 3)):
        degree = s + (q-1)//2
        graph = [field.power(x, degree) for x in range(q)]
        if len(set(graph)) != q:
            raise ArithmeticError(("non-permutation", s, n))
        singular = branch_criterion(field, s, n)
        if n == 2:
            if set(singular[1:]) != {0, 2}:
                raise ArithmeticError(("quadratic branches", s))
            subfield = {x for x in range(q) if field.power(x, s) == x}
            if len(subfield) != s or any(field.power(c, degree) != c for c in subfield):
                raise ArithmeticError("Base-field homogeneity failed")
            # One outside value and its s-1 nonzero scalar multiples cover all
            # nonzero classes modulo the base field; the graph also contains 0.
            for a in range(q):
                if not any(field.add(y, field.negative[field.mul(a, x)]) not in subfield
                           for x, y in enumerate(graph)):
                    raise ArithmeticError(("quadratic witness", a))
            print(f"F_{q}: d={degree} permutes; the F_{s} parameter set covers all {q} slopes")
        else:
            if max(singular[1:]) > 1:
                raise ArithmeticError(("invertible branch", s))
            # x -> u*x identifies slopes differing by a (degree-1)st power.
            classes = gcd(degree-1, q-1)
            sizes = [len({field.add(y, field.negative[field.mul(a, x)])
                          for x, y in enumerate(graph)}) for a in field.powers[:classes]]
            if min(sizes) < (q-1)//2:
                raise ArithmeticError(("cubic miss bound", min(sizes)))
            print(f"F_{q}: d={degree} permutes; {classes} nonzero slope classes, "
                  f"minimum value-set size {min(sizes)}")


def composite_index():
    # Four branches, every slope has exactly one singular branch. Select one
    # slope of each possible norm and test every rational shift and parameter.
    field = Field(5, [2, 0, 1])
    if set(branch_criterion(field, 5, 3, m=4)[1:]) != {1}:
        raise ArithmeticError("Expected one singular branch at every nonzero slope")
    slopes = field.powers[:4]
    if len({field.power(a, 31) for a in slopes}) != 4:
        raise ArithmeticError("Expected all four norms")
    cases = degenerate_transport(field, slopes, range(125), range(125), s=5, m=4)
    print(f"F_125: index 4, all 124 nonzero slopes have one singular branch; {cases} fibre checks")


if __name__ == "__main__":
    for prime in (3, 5):
        square_model(prime)
    odd_cubic_base()
    composite_index()
    shared_field()
