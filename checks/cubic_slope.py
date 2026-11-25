"""Finite example of the branch-avoidance argument for vertical translates."""

from math import isqrt


def branch_values(q, u, shifts):
    # The two critical points are x = ±u. The intercept is x³ - m*x - a.
    return {(sign * 2 * u**3 - a) % q for a in shifts for sign in (-1, 1)}


def main():
    q = 200003
    shifts = (0, 4, 32)
    if q % 3 != 2 or any(q % d == 0 for d in range(2, isqrt(q) + 1)):
        raise ValueError("The example requires a prime congruent to 2 modulo 3.")

    k = len(shifts)
    u = next(s for s in range(1, q) if len(branch_values(q, s, shifts)) == 2*k)
    m = 3*u*u % q
    image = {(x**3 - m*x) % q for x in range(q)}
    escaping = [b for b in range(q) if all((b + a) % q not in image for a in shifts)]
    # Independently check the first witness against the original line equations.
    b = escaping[0]
    if any((x**3 - a - m*x - b) % q == 0 for a in shifts for x in range(q)):
        raise ArithmeticError("The claimed missing line intersects a translate.")
    if (u, len(image), len(escaping), b) != (3, (2*q-1)//3, 7339, 15):
        raise ArithmeticError("Unexpected slope, image size, count or first witness.")

    print(f"F_{q}, shifts {shifts}: first admissible u = {u}, slope m = {m}")
    print(f"{len(image)} cubic values; {len(escaping)} missing lines of this slope")
    print(f"First missing line: y = {m}x + {b}")


if __name__ == "__main__":
    main()
