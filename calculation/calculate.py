"""Evaluate the all-alphabet lower bound and compare with Almanac records."""
import argparse
from fractions import Fraction
from math import ceil, factorial, lcm
from lower.collision import first_collision, public_return

Q = Fraction

# Public individual bounds, checked 25 November 2026 (Korea).
# S(1) and S(2) follow directly. The Almanac records table starts at S(3).
RECORDS = (0, 1, 3, 9, 33, 153, 872, 5899, 46134, 408470, 4033379,
           43917904, 522622401, 6746627048, 93891141157)


def old_parameters(n):
    initial = {8: (10, Q(46, 3)), 9: (15, Q(287, 12)), 10: (Q(521, 80), Q(359, 40)),
               11: (21, Q(263, 12)), 12: (28, Q(195, 4))}
    if n in initial:
        return initial[n]
    k = n - 1
    m, residue = divmod(k, 3)
    if residue == 0:
        return alternating_parameters(m, 2 * public_return(m))
    if residue == 1:
        ret = (3*m + 1, lcm((2*m+1)//3, (7*m+2)//3), 3*m + 1,
               lcm((7*m+3)//6, (11*m+3)//6), lcm((2*m+1)//3, (7*m+2)//6),
               lcm((7*m+1)//6, (11*m+5)//6))[m % 6]
        return m * (2*m + 1), 2*m*m + 2*m - 2 - Q(1, ret)
    return (m + 1) * (2*m + 1), 4*m*m + 5*m - Q(5, 2)


def alternating_parameters(m, cutoff):
    return 2*m + Q(1, 2) + Q(1, 2*cutoff), 4*m - 3 - Q(1, cutoff)


def lower(n, parameters):
    p, t = map(Q, parameters)
    excess = (2*factorial(n-2) - 2*(n-2) - 4*p/t) / (n*n - 4*n + 1 - 2*(n-1)/t)
    return sum(factorial(n-j) for j in range(3)) + n - 3 + ceil(excess)


def baseline(n):
    if n < 1:
        raise ValueError("Use an alphabet with at least one symbol.")
    if n < 8:
        # Values of the cited general bounds at their small arguments.
        return (0, 1, 3, 9, 33, 153, 870, 5895)[n]
    return lower(n, old_parameters(n))


def general_bound(n, scan=True):
    result = baseline(n)
    if n >= 10 and n % 3 == 1:
        m = (n - 1) // 3
        period = public_return(m)
        cutoff = {3: 3, 4: 3, 5: 7}.get(m, period)
        if scan:
            hits = (first_collision(m, swapped) for swapped in (False, True))
            cutoff = max(hit.pair if hit else period for hit in hits)
        return max(result, lower(n, alternating_parameters(m, 2*period-1)),
                   lower(n, alternating_parameters(m, 2*cutoff-1)))
    return result


def evaluate(n, scan=True):
    result = general_bound(n, scan)
    previous = baseline(n)
    print(f"n={n}  baseline={previous:,}  general={result:,}  gain={result-previous:,}")
    if n < len(RECORDS):
        print(f"  individual={RECORDS[n]:,}  individual minus general={RECORDS[n]-result:,}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="*", default=list(range(1, 15)))
    parser.add_argument("--closed", action="store_true", help="use the closed cutoff without enumerating slots")
    arguments = parser.parse_args()
    for alphabet_size in arguments.n:
        evaluate(alphabet_size, scan=not arguments.closed)
