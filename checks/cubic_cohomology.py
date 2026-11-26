"""Test the cubic H¹ bounds using only the meridian commutations (Python 3.8+).

The generators are x_1,...,x_ℓ,x_∞,y_1,...,y_ℓ,y_∞. Retaining just
[x_i,y_j]=1 for i != j gives a group surjecting onto the configuration
group, hence an upper bound for its H¹. All matrices have integral lifts.
Reducing modulo 101 can only lower the rank of the relation matrix.
The coboundary dimension is the same in both characteristics since
the representation is an outer tensor product of irreducible S_3 modules.
No inference for untested ℓ is made from these computations.
"""

import argparse
from math import comb
from time import perf_counter


PRIME = 101
TRIVIAL = ((1,),)
NEGATE = ((-1,),)
# Reflections (12) and (23) in the basis e1-e2, e2-e3.
FIRST = ((-1, 1), (0, 1))
SECOND = ((1, 0), (1, -1))
IDENTITY = ((1, 0), (0, 1))


def tensor_rows(matrices):
    """Sparse rows of the Kronecker product, indexed by tensor basis words."""
    rows = [{0: 1}]
    for matrix in matrices:
        dimension = len(matrix)
        rows = [
            {column * dimension + j: a * b for column, a in row.items()
             for j, b in enumerate(local_row) if b}
            for row in rows for local_row in matrix
        ]
    return rows


def defect_rows(matrices):
    """Sparse rows of 1 minus the tensor product."""
    result = []
    for i, row in enumerate(tensor_rows(matrices)):
        defect = {j: -value for j, value in row.items()}
        defect[i] = defect.get(i, 0) + 1
        result.append({j: value for j, value in defect.items() if value})
    return result


def generator_defects(trivial, sign, standard):
    types = ([(TRIVIAL, TRIVIAL, TRIVIAL)] * trivial
             + [(TRIVIAL, NEGATE, NEGATE)] * sign
             + [(IDENTITY, FIRST, SECOND)] * standard)
    identities, first, second = map(list, zip(*types))

    def finite(actions):
        defects = []
        for i, action in enumerate(actions):
            matrices = identities.copy()
            matrices[i] = action
            defects.append(defect_rows(matrices))
        return defects

    # At infinity each factor is the transposition at the opposite
    # finite meridian, by commutation and the S_3 centralizer.
    return finite(first) + [defect_rows(second)], finite(second) + [defect_rows(first)]


def relation_rows(left, right):
    """(1 - y_j)D(x_i) - (1 - x_i)D(y_j) for every i != j."""
    dimension = len(left[0])
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            if i == j:
                continue
            for y_row, x_row in zip(y, x):
                row = {i * dimension + k: value for k, value in y_row.items()}
                offset = (len(left) + j) * dimension
                row.update({offset + k: -value for k, value in x_row.items()})
                yield row


def rank_mod_prime(rows):
    """Incremental sparse elimination, with normalized rows indexed by pivot."""
    basis = {}
    for row in rows:
        row = {column: value % PRIME for column, value in row.items() if value % PRIME}
        while row:
            column = min(row)
            leading = row[column]
            if column not in basis:
                inverse = pow(leading, -1, PRIME)
                basis[column] = {k: v * inverse % PRIME for k, v in row.items()}
                break
            for k, value in basis[column].items():
                remainder = (row.get(k, 0) - leading * value) % PRIME
                if remainder:
                    row[k] = remainder
                else:
                    row.pop(k, None)
    return len(basis)


def check_type(trivial, sign, standard):
    left, right = generator_defects(trivial, sign, standard)
    dimension = len(left[0])
    generators = left + right
    # D_z(g) = (1-g)z. Check its rank separately from the relations.
    inner = rank_mod_prime(row for generator in generators for row in generator)
    expected_inner = dimension - int(sign == standard == 0)
    if inner != expected_inner:
        raise ArithmeticError(f"Unexpected coboundary rank for {(trivial, sign, standard)}")
    relations = rank_mod_prime(relation_rows(left, right))
    upper = len(generators) * dimension - relations - inner
    ell = trivial + sign + standard
    if sign == 0:
        bound = 4 * ell + 2 if standard else 6 * ell + 2
    elif sign == 1:
        bound = 2
    elif sign == 2 and standard == 0:
        bound = 1
    else:
        bound = 0
    if not 0 <= upper <= bound:
        raise ArithmeticError(f"H¹ bound failed for {(trivial, sign, standard)}: {upper}")
    return upper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-ell", type=int, default=6)
    limit = parser.parse_args().max_ell
    if limit < 1:
        parser.error("--max-ell must be positive")
    started = perf_counter()
    total = 0
    for ell in range(1, limit + 1):
        nontrivial = []
        weighted_sum = 0
        for sign in range(ell + 1):
            for standard in range(ell - sign + 1):
                upper = check_type(ell - sign - standard, sign, standard)
                if sign or standard:
                    nontrivial.append(upper)
                    multiplicity = comb(ell, sign) * comb(ell - sign, standard)
                    weighted_sum += multiplicity * upper
                else:
                    trivial_upper = upper
                total += 1
        sum_bound = (4 * ell + 2) * (2**ell - 1) + ell * 2**ell + comb(ell, 2)
        if weighted_sum > sum_bound:
            raise ArithmeticError(f"Summed H¹ bound failed for ell={ell}")
        print(f"ell={ell}: {len(nontrivial) + 1} types, trivial bound {trivial_upper}, "
              f"largest nontrivial bound {max(nontrivial)}, summed bound {weighted_sum}")
    print(f"{total} types up to permutation passed in {perf_counter() - started:.2f}s.")


if __name__ == "__main__":
    main()
