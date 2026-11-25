"""Exhaustive check of B(47, 3) and its optimal parameter sets (Python 3)."""

from itertools import combinations
from math import comb


P = 47
REPRESENTATIVE = (0, 1, 3, 15, 33)


def line_masks():
    """Bit m*P+b records intersection with the line y=m*x+b."""
    masks = []
    for a in range(P):
        # On y=x^3-a, the intercept at x for slope m is x^3-a-m*x.
        covered = 0
        for m in range(P):
            for x in range(P):
                b = (x**3 - a - m*x) % P
                covered |= 1 << (m*P + b)
        masks.append(covered)
    return masks


def anchored_solutions(size, masks):
    """Enumerate sorted size-element sets containing zero, once each."""
    all_lines = (1 << (P*P)) - 1
    solutions = set()
    for rest in combinations(range(1, P), size - 1):
        covered = masks[0]
        for a in rest:
            covered |= masks[a]
        if covered == all_lines:
            solutions.add((0,) + rest)
    return solutions


def affine_image(points, u, v):
    return tuple(sorted((u*a + v) % P for a in points))


def main():
    masks = line_masks()
    fours = anchored_solutions(4, masks)
    fives = anchored_solutions(5, masks)
    for size, solutions in [(4, fours), (5, fives)]:
        print(f"{size}-sets containing 0: {len(solutions)} / {comb(P-1, size-1)} block")
    if fours or len(fives) != 230:
        raise RuntimeError("Unexpected anchored enumeration")

    # Translating the parameters translates the curves vertically. Every
    # blocking set can be anchored by subtracting one of its members.
    all_optima = {affine_image(s, 1, v) for s in fives for v in range(P)}
    if 5 * len(all_optima) != P * len(fives):
        raise RuntimeError("Translation double count failed")

    orbit = {affine_image(REPRESENTATIVE, u, v)
             for u in range(1, P) for v in range(P)}
    if all_optima != orbit or len(orbit) != 2162:
        raise RuntimeError("Optimal sets differ from the proposed affine orbit")
    print(f"All optimal sets: {len(all_optima)} = {len(fives)} * {P} / 5")
    print(f"Affine orbit of {REPRESENTATIVE}: {len(orbit)} distinct sets, exact match")
    print("B(47, 3) = 5")


if __name__ == "__main__":
    main()
