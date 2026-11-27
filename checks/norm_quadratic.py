"""Finite part of the norm-power argument in odd quadratic extensions.

Run with Python 3. For K = F_s(w), w^2 = k, project x+yw to x. Check
that the projection of N(z)^m + a*z attains every element of F_s for
each positive exponent class m modulo s-1 and every nonzero slope a.
"""


def base_tables(s):
    def add(a, b):
        if s != 9:
            return (a + b) % s
        return (a % 3 + b % 3) % 3 + 3 * ((a // 3 + b // 3) % 3)

    def multiply(a, b):
        if s != 9:
            return a * b % s
        # F_9 = F_3[i], i^2 = -1, with digit encoding x + 3*y.
        x, y = a % 3, a // 3
        u, v = b % 3, b // 3
        return (x * u - y * v) % 3 + 3 * ((x * v + y * u) % 3)

    return ([[add(a, b) for b in range(s)] for a in range(s)],
            [[multiply(a, b) for b in range(s)] for a in range(s)])


def verify(s):
    add, mul = base_tables(s)
    negative = [row.index(0) for row in add]
    squares = {mul[x][x] for x in range(s)}
    k = next(x for x in range(1, s) if x not in squares)
    points = [(x, y) for x in range(s) for y in range(s)]
    norm = [add[mul[x][x]][negative[mul[k][mul[y][y]]]] for x, y in points]
    projected_slopes = [
        [add[mul[a][x]][mul[mul[k][b]][y]] for x, y in points]
        for a, b in points if (a, b) != (0, 0)
    ]
    power = norm.copy()
    for m in range(1, s):
        for index, linear_part in enumerate(projected_slopes, start=1):
            image = {add[u][v] for u, v in zip(power, linear_part)}
            if len(image) != s:
                raise ValueError((s, m, points[index], sorted(set(range(s)) - image)))
        power = [mul[u][v] for u, v in zip(power, norm)]
    return (s - 1) * (s * s - 1)


if __name__ == "__main__":
    total = 0
    for size in (3, 5, 7, 9, 11, 13, 17, 19, 23):
        count = verify(size)
        print(f"F_{size}: {count} exponent-slope pairs passed")
        total += count
    print(f"Total: {total}")
