"""Check the two-parameter cubic count over four prime fields (Python 3.8+)."""

from collections import Counter


def power_mod_cubic(exponent, m, c, p):
    """Return X^exponent modulo X^3 - mX - c, in increasing degree order."""
    def multiply(a, b):
        coeffs = [0] * 5
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                coeffs[i + j] += ai * bj
        for k in (4, 3):
            coeffs[k - 3] += c * coeffs[k]
            coeffs[k - 2] += m * coeffs[k]
        return tuple(ai % p for ai in coeffs[:3])

    result = (1, 0, 0)
    base = (0, 1, 0)
    while exponent:
        if exponent % 2:
            result = multiply(result, base)
        base = multiply(base, base)
        exponent //= 2
    return result


def three_cycle(m, c, p):
    """All roots lie in F_(p^3), and they do not all lie in F_p."""
    x = (0, 1, 0)
    return (power_mod_cubic(p**3, m, c, p) == x
            and power_mod_cubic(p, m, c, p) != x)


def check_field(p):
    cuberoot = {x**3 % p: x for x in range(p)}
    square_slopes = {3*u*u % p for u in range(1, p)}
    half = pow(2, -1, p)
    quarter = pow(4, -1, p)
    images = [{(x**3 - m*x) % p for x in range(p)} for m in range(p)]
    normalized_cycles = [three_cycle(3, t, p) for t in range(p)]

    def misses(m, b, shifts):
        return all((b + s) % p not in images[m] for s in shifts)

    # Bary-Soroker--Stix, Theorem 1.4, after removing the quadratic
    # coefficient of a monic cubic. Each depressed cubic occurs p times.
    expected_twins = (p*p - p - 2) // 9
    for h in range(1, p):
        actual = sum(misses(m, b, (0, h)) for m in range(p) for b in range(p))
        if actual != expected_twins:
            raise ArithmeticError(f"Twin count failed for p={p}, h={h}")

    for shifts in ((0,), (0, 1), (1, 3, 7), (0, 1, 3, 5)):
        excluded = {-s % p for s in shifts}
        endpoints = [v for v in range(p) if v not in excluded]
        counts = Counter()
        open_size = 0
        for v in endpoints:
            for w in endpoints:
                if v == w:
                    continue
                open_size += 1
                u_cubed = (v - w) * quarter % p
                u = cuberoot[u_cubed]
                m = 3*u*u % p
                b = (v + w) * half % p
                inv_difference = pow(v - w, -1, p)
                all_cycles = True
                for s in shifts:
                    t = 2 * (v + w + 2*s) * inv_difference % p
                    if t * u_cubed % p != (b + s) % p or t in (2, p - 2):
                        raise ArithmeticError("Incorrect normalization or branch exclusion")
                    all_cycles = all_cycles and normalized_cycles[t]
                if all_cycles:
                    counts[m, b] += 1

        if open_size != (p - len(shifts)) * (p - len(shifts) - 1):
            raise ArithmeticError("Unexpected open-set cardinality")
        direct = {(m, b): 2 for m in square_slopes for b in range(p)
                  if misses(m, b, shifts)}
        if counts != direct:
            raise ArithmeticError(f"Ordered-pair and direct line counts differ for {p}, {shifts}")
        print(f"F_{p}, S={shifts}: {open_size} pairs in U, "
              f"{sum(counts.values())} three-cycle pairs, {len(direct)} missing lines")
    print(f"F_{p}: {expected_twins} all-slope twins for each nonzero shift")


if __name__ == "__main__":
    for prime in (11, 17, 41, 47):
        check_field(prime)
