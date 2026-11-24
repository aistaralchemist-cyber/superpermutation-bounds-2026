"""Independent exact evaluations for the dated comparison. Run with Python 3.8+."""
from fractions import Fraction as Q
from math import factorial


def transfer(n, p, t):
    numerator = (2 * factorial(n - 2) - 2 * (n - 2)) * t - 4 * p
    denominator = (n * n - 4 * n + 1) * t - 2 * (n - 1)
    assert denominator > 0
    ceiling = -((-numerator) // denominator)
    return sum(factorial(k) for k in (n, n-1, n-2)) + n - 3 + ceiling


def prices(m, d):
    return 2*m + Q(1, 2) + Q(1, 2*d), 4*m - 3 - Q(1, d)


def formula_comparison(n):
    if n <= 7:
        old = (1, 3, 9, 33, 153, 870, 5895)[n-1]
        return old, old
    published = {8: (10, Q(46, 3)), 9: (15, Q(287, 12)), 10: (Q(521, 80), Q(359, 40)),
                 11: (21, Q(263, 12)), 12: (28, Q(195, 4)), 14: (36, 38 - Q(1, 15))}
    if n % 3 != 1:
        v = transfer(n, *published[n])
        return v, v
    s = n - 1
    m = s // 3
    if s % 7:
        u = next(u for u in range(1, s) if 7*u % s == 1)
        period = u * (s-u)
    else:
        period = 2*s // 7
    old = transfer(n, *published.get(n, prices(m, 2*period)))
    cutoff = {3: 3, 4: 3, 5: 7}.get(m, period)
    return old, max(old, transfer(n, *prices(m, 2*period-1)), transfer(n, *prices(m, 2*cutoff-1)))


if __name__ == "__main__":
    for n in [*range(1, 15), 16, 19, 22]:
        p, l = formula_comparison(n)
        print(n, f"{p:,}", f"{l:,}", f"{l-p:+,}")
    lower14, old_word, new_word = 93891141157, 93904707912, 93904707285
    print("14-symbol widths:", old_word-lower14, new_word-lower14, "saving", old_word-new_word)
    print("Upper threshold", 2904*10400**2*6**20*4**2)
    print("Relative reduction in upper error allowance", Q(214-86, 214))
