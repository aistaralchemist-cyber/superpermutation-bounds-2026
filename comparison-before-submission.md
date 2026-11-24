# Comparison against the Superpermutation Almanac

Jaehun Jung · 25 November 2026, Korea Standard Time

## The general lower bound

Let P be the baseline used in the paper and L the new closed formula. For n = 1, 2 the baseline uses the elementary exact lengths. For n = 3 through 7 the paper specializes the published Hunter–Raudvere, Kisic–Halfar and Halfar bounds. From n = 8 onward P is Pantone’s bound 34. The last column records the individual lower bounds on the Almanac records page at the time of comparison. [Hunter–Raudvere](https://superpermutations.com/b/6) · [Kisic–Halfar](https://superpermutations.com/b/7) · [Halfar](https://superpermutations.com/b/9) · [Pantone](https://superpermutations.com/b/34) · [Almanac records](https://superpermutations.com/)

| n | Earlier formula P | New formula L | L − P | Individual lower bound or exact value |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 | 1 |
| 2 | 3 | 3 | 0 | 3 |
| 3 | 9 | 9 | 0 | 9 |
| 4 | 33 | 33 | 0 | 33 |
| 5 | 153 | 153 | 0 | 153 |
| 6 | 870 | 870 | 0 | 872 |
| 7 | 5,895 | 5,895 | 0 | 5,899 |
| 8 | 46,130 | 46,130 | 0 | 46,134 |
| 9 | 408,469 | 408,469 | 0 | 408,470 |
| 10 | 4,033,374 | 4,033,375 | +1 | 4,033,379 |
| 11 | 43,917,903 | 43,917,903 | 0 | 43,917,904 |
| 12 | 522,622,380 | 522,622,380 | 0 | 522,622,401 |
| 13 | 6,746,626,531 | 6,746,626,690 | +159 | 6,746,627,048 |
| 14 | 93,891,141,149 | 93,891,141,149 | 0 | 93,891,141,157 |

The published evaluation table for bound 34 lists all seven baseline values from 8 to 14. The independent arithmetic script reproduces each value and every new evaluation in the paper. The fourteen new values also agree with the Lean kernel evaluation. At seven symbols Halfar separately reports a computer-assisted lower bound of 5,901. [Independent calculation](check-comparison.py) · [Kernel evaluation](https://github.com/aistaralchemist-cyber/superpermutation-bounds-2026/blob/29b4ac619862ccf9c5a15dacfbb8ed80ba6a25b2/source/GeneralValues.lean) · [Halfar’s seven-symbol proof materials](https://github.com/jhalfar/superpermutations/tree/8e3c02b5234b49a1422751f86f9e472706082374/proofs/n7_5901)

For **every** n congruent to 1 modulo 3 with n ≥ 16, the proof gives L(n) ≥ P(n) + 4. Exact examples follow.

| n | Earlier formula P | New formula L | Gain |
|---:|---:|---:|---:|
| 16 | 22,318,554,295,253 | 22,318,554,323,969 | 28,716 |
| 19 | 128,405,663,871,800,048 | 128,405,663,871,842,927 | 42,879 |
| 22 | 1,177,536,880,652,160,293,837 | 1,177,536,880,668,122,668,017 | 15,962,374,180 |

## The general upper bound

Set A(n) = n! + (n−1)! + (n−2)! + 2(n−4)! and E(n) = (n−4)!(ln n)^(1/10)n^(−1/20). Halfar’s bound 51 gives S(n) ≤ A(n) + 214 E(n). The new proof gives S(n) ≤ A(n) + 86 E(n) from the same integer threshold, 2904·10400²·6²⁰·4² = 18,374,193,301,302,754,400,010,240,000. The error allowance decreases by exactly 128 E(n), or 64/107 of the old allowance (about 59.81%). The exponents and the center are unchanged. The lower side of the two-sided statement follows from the earlier lower estimate already used by Halfar. This large-alphabet theorem does not apply to 14. [Halfar’s bound 51](https://superpermutations.com/b/51) · [Halfar’s proof](https://github.com/jhalfar/superpermutation-almanac-lean/blob/4392df9764a5be7e5bd4dc15a414defe94077eaf/lean/Asym22/LogRate.lean)

## The fourteen-symbol interval

| Comparison | Earlier | New | Change |
|---|---:|---:|---:|
| General lower formula at n = 14 | 93,891,141,149 | 93,891,141,149 | 0 |
| Individual lower proof, bound 32 to accepted bound 52 | 93,891,141,150 | 93,891,141,157 | +7 |
| Word length, W-0165 to submitted W-0166 | 93,904,707,912 | 93,904,707,285 | −627 |
| Interval width with accepted bound 52 fixed | 13,566,755 | 13,566,128 | −627 |

The width from the older pair of endpoints (bound 32 and W-0165) was 13,566,762. Updating both endpoints saves 634 letters of uncertainty. The Almanac record page displayed W-0165 when these comparisons were made. W-0166 was under verification. The new word’s reproduction and full scan are included in the published materials. [Bound 32](https://superpermutations.com/b/32) · [Bound 52](https://superpermutations.com/b/52) · [W-0165](https://superpermutations.com/w/W-0165) · [14-symbol records](https://superpermutations.com/n/14) · [Published word and certificates](https://github.com/aistaralchemist-cyber/superpermutation-bounds-2026/tree/cd6a1bd4609e5ee4fbff74eac99bfd58fe63c6aa)
