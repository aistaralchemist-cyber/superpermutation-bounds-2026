"""Exact occupied-row collisions for the two orientations of Pantone's extremal pair."""
from dataclasses import dataclass
from fractions import Fraction
from math import ceil, factorial


def public_return(m):
    n = 3 * m
    if n % 7 == 0:
        return 2 * n // 7
    u = pow(7, -1, n)
    return u * (n - u)


@dataclass(frozen=True)
class Witness:
    pair: int
    earlier: tuple[int, int, int]
    later: tuple[int, int, int]


def first_collision(m, swapped=False):
    """Return first certified pair, with cells numbered from zero; None means use the known return."""
    if m < 3:
        raise ValueError("m must be at least 3")
    n = 3 * m
    long, short = 2*m-1, 2*m-2
    first, second = (short, long) if swapped else (long, short)
    circuit = (False,) * (first-1) + (True,) + (False,) * (second-1) + (True,)
    identity = tuple(range(n+1))
    inv_g = (0, n, n-2, n-1, 2, 1, *range(3,n-2))
    inv_rho = (0, 1, n, *range(2,n))
    moves = (inv_g, tuple(inv_g[v] for v in inv_rho))
    y = (*range(3,n+1),2,1,0)
    u = (1,*range(3,n),2,n,0)
    base_rows = (y,) + tuple(u[j:n-1]+u[:j]+u[n-1:] for j in range(n-3))
    norm = identity
    seen = {}
    for pair in range(1, public_return(m)+1):
        for within, bit in enumerate(circuit):
            cell = (pair-1)*len(circuit)+within
            # Only the first full row of a shortened cell is needed for the current soundness lemma.
            for off, row in enumerate(base_rows[:2] if bit else base_rows):
                labels = tuple(norm[v] for v in row[:-1])
                origin = labels.index(1)
                key = labels[origin:] + labels[:origin]
                count = n-2 if off == 0 else n
                if key in seen:
                    old_cell, old_off, old_origin, old_count = seen[key]
                    for new_slot in range(count):
                        old_slot = (new_slot+old_origin-origin) % n
                        if old_slot < old_count:
                            return Witness(pair,(old_cell,old_off,old_slot),(cell,off,new_slot))
                    raise AssertionError("Two intervals of more than half the cycle overlap.")
                seen[key] = cell, off, origin, count
            norm = tuple(norm[v] for v in moves[bit])
    return None


def lower(m,r):
    n = 3*m+1
    d = 2*r-1
    p = 2*m + Fraction(1,2) + Fraction(1,2*d)
    t = 4*m - 3 - Fraction(1,d)
    correction = (2*factorial(n-2) - 2*(n-2) - 4*p/t) / (n*n - 4*n + 1 - 2*(n-1)/t)
    return sum(factorial(n-j) for j in range(3)) + n-3 + ceil(correction)


if __name__ == "__main__":
    import sys
    for m in map(int, sys.argv[1:] or range(3,10)):
        r0 = public_return(m)
        hit = [first_collision(m, swapped) for swapped in (False,True)]
        r = max([w.pair if w else r0 for w in hit])
        print(m,3*m+1,r0,r,lower(m,r),lower(m,r)-lower(m,r0),*hit,flush=True)
