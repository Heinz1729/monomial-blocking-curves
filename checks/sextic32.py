"""Two exhaustive enumerations of vertical sextic translates over F_32."""
from itertools import combinations
from math import comb


Q = 32
FIELD = range(Q)
MODULUS = 0b100101  # T^5 + T^2 + 1; labels give the five polynomial coefficients.


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & Q:
            a ^= MODULUS
    return result


MUL = [[multiply(a, b) for b in FIELD] for a in FIELD]
CUBE = [MUL[x][MUL[x][x]] for x in FIELD]
SIXTH = [MUL[y][y] for y in CUBE]


def anchored_by_lines(size, hits):
    """Bit 32*m+b means the selected curves meet the actual line y=mx+b."""
    all_lines = (1 << (Q * Q)) - 1
    solutions = set()
    for rest in combinations(range(1, Q), size - 1):
        covered = hits[0]
        for a in rest:
            covered |= hits[a]
        if covered == all_lines:
            solutions.add((0,) + rest)
    return solutions


def parameter_rows():
    # x=c*z changes the slope to c^5 and the intercept scale to c^6.
    # Both powers permute F_32^*. Varying the intercept then gives all shifts.
    image = {SIXTH[x] ^ x for x in FIELD}
    if {v for v in SIXTH} != set(FIELD) or len(image) != 16:
        raise ArithmeticError("Incorrect sextic value sets")
    fifth = {MUL[x][MUL[MUL[x][x]][MUL[x][x]]] for x in range(1, Q)}
    if fifth != set(range(1, Q)):
        raise ArithmeticError("Missing slope")
    return {sum(1 << (MUL[c][x] ^ b) for x in image)
            for c in range(1, Q) for b in FIELD}


def normalized_by_rows(size, rows):
    # The candidates already contain 0 and 1. Remaining rows need a witness.
    constraints = sorted(row for row in rows if row & 3 == 0)
    solutions = set()
    for rest in combinations(range(2, Q), size - 2):
        selected = sum(1 << x for x in rest)
        if all(selected & row for row in constraints):
            solutions.add((0, 1) + rest)
    return solutions


def affine_orbit(points):
    return {tuple(sorted(MUL[u][x] ^ v for x in points))
            for u in range(1, Q) for v in FIELD}


def main():
    # Every nonzero residue acts bijectively in the polynomial quotient.
    if any(len(set(MUL[a])) != Q for a in range(1, Q)):
        raise ArithmeticError("The chosen polynomial does not define a field")
    hits = [0] * Q
    for a in FIELD:
        for m in FIELD:
            for x in FIELD:
                b = SIXTH[x] ^ a ^ MUL[m][x]
                hits[a] |= 1 << (Q * m + b)
    rows = parameter_rows()
    # Compare the actual nonhorizontal lines to the blocks of the Segre design
    # of Ding and Tang, including both the block count and the triple index.
    line_rows = {
        sum(1 << a for a in FIELD if (hits[a] >> line) & 1)
        for line in range(Q, Q * Q)
    }
    if line_rows != rows or len(rows) != 992:
        raise ArithmeticError("The 992 nonhorizontal lines must give 992 distinct blocks")
    for a, b, c in combinations(FIELD, 3):
        triple = (1 << a) | (1 << b) | (1 << c)
        if sum((row & triple) == triple for row in rows) != 112:
            raise ArithmeticError("Triple multiplicity differs from the Segre design")
    for size, counts in [(6, (0, 0)), (7, (2387, 462))]:
        anchored = anchored_by_lines(size, hits)
        normalized = normalized_by_rows(size, rows)
        if {s for s in anchored if 1 in s} != normalized:
            raise ArithmeticError("Independent line and value-set tests disagree")
        if (len(anchored), len(normalized)) != counts:
            raise ArithmeticError("Unexpected count")
        print(f"size {size}: {len(anchored)}/{comb(31, size-1)} containing 0; "
              f"{len(normalized)}/{comb(30, size-2)} containing 0,1")
    # Every set of size at most six can be extended to a six-element set.
    # Translations take every nonempty solution to one containing zero.
    all_sevens = {tuple(sorted(a ^ v for a in s)) for s in anchored for v in FIELD}
    remaining = set(normalized)
    classified = set()
    orbit_index = {}
    reps = []
    while remaining:
        rep = min(remaining)
        orbit = affine_orbit(rep)
        if len(orbit) != 992 or not orbit <= all_sevens or classified & orbit:
            raise ArithmeticError("Incorrect orbit or stabilizer")
        reps.append(rep)
        classified.update(orbit)
        for points in orbit:
            orbit_index[points] = rep
        remaining.difference_update(orbit)
    if classified != all_sevens or len(reps) != 11 or len(classified) != 10912:
        raise ArithmeticError("Incomplete classification")
    print("B(32,6)=7; 10,912 optima in 11 free affine orbits of size 992.")
    print("Representatives in the polynomial basis:")
    for rep in reps:
        print(*rep)
    # Squaring normalizes the affine group and generates Gal(F_32/F_2).
    unseen = set(reps)
    cycles = []
    while unseen:
        start = min(unseen)
        rep = start
        cycle = []
        while rep in unseen:
            unseen.remove(rep)
            cycle.append(rep)
            rep = orbit_index[tuple(sorted(MUL[x][x] for x in rep))]
        if rep != start:
            raise ArithmeticError("Frobenius did not permute the affine orbits")
        cycles.append(len(cycle))
    if sorted(cycles) != [1, 5, 5]:
        raise ArithmeticError("Unexpected semilinear orbit lengths")
    print("Under the semilinear group: three orbits of sizes 992, 4960, 4960.")


if __name__ == "__main__":
    main()
