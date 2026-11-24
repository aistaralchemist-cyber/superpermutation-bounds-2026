# Interior alternating chains and lower bounds for superpermutations

Jaehun Jung · Independent Researcher, Republic of Korea · 25 November 2026

The closed expression improves the published general lower formula on an infinite residue class. At every size through fourteen the individual lower bounds are at least as strong as the new expression.

[English manuscript](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Closed formula](source/GeneralLower.lean) · [Submission theorem](AlmanacSolution.lean)

Let S(n) be the minimum length of a word containing all permutations of n symbols as contiguous substrings. For n = 3m + 1, an interior alternating run has at most 2r − 1 chains whenever both orders of r completed pairs are excluded. Applied at the published return order, this raises Pantone's general integer lower bound by at least four for every n congruent to one modulo three from n = 16 onward. Earlier occupied-slot collisions yield 4,033,375 at n = 10, 6,746,626,690 at n = 13, and 22,318,554,323,969 at n = 16. Their gains over the previous general formula are 1, 159, and 28,716, respectively. The manuscript gives the full formula including all other alphabet sizes.

The stronger individual lower bounds registered at 10 and 13 are 4,033,379 and 6,746,627,048. At 14 the general formula gives 93,891,141,149 and Jung's earlier registered individual certificate gives 93,891,141,157. [Almanac individual records](https://superpermutations.com/) · [Pantone's general baseline](https://superpermutations.com/b/34) · [Earlier fourteen-symbol lower certificate](https://superpermutations.com/b/52)

## Verification

The root uses the Almanac Lean 4.35.0 batch format. It declares one general lower bound. Finite evaluations are consequences recorded in the manuscript. Mathlib is pinned in the Lake configuration. The theorem in the submission namespace combines the unrestricted word-level inequality for the closed numerical function with the strict comparison on the infinite residue class. The type uses Almanac's contiguous-factor predicate. The two components can be used independently.

```sh
lake exe cache get
lake build AlmanacSolution
lake env leanchecker -v AlmanacSolution
python3 -B calculation/calculate.py --closed
```

Core declarations and their roles are given below.

| File | Result |
|---|---|
| [InteriorCut](source/InteriorCut.lean) | The following chain supplies the final short separator of an interior alternating run. |
| [CutPayment](source/CutPayment.lean) | Bound on the sum of chain lengths with an arbitrary positive cap. |
| [SlotGeometry](source/SlotGeometry.lean) | Coordinate equality of occupied slots in different rows excludes the two-row configuration. |
| [CollisionExamples](source/CollisionExamples.lean) | Six explicit collision certificates covering both orientations at n = 10, 13, and 16. |
| [JungComparison](source/JungComparison.lean) | Direct inequality between the closed formula and the published bound after rounding on the infinite residue class. |
| [GeneralLower](source/GeneralLower.lean) | Unconditional closed-form and search-based lower bounds for arbitrary words. |
| [GeneralValues](source/GeneralValues.lean) | Direct kernel evaluation of the closed formula at n = 1 through 14. |

The three files named AlmanacDefs, AlmanacStatement and AlmanacChallenge are scaffold files. The registry supplies its own versions when it checks a submission. The solution imports AlmanacDefs and the research modules. The research theorem and the equivalence of the covering predicates do not depend on the scaffold challenge.

## Attribution and provenance

The proof extends Pantone's chain-packing framework. The small-alphabet branch uses results of Hunter and Raudvere, Kisic and Halfar, and Halfar. The source closure is vendored into a single Lake project to give each module one origin and make the archived SHA reproducible. The inventory lists the source and SHA-256 of each file. The original licenses and attribution notices accompany the sources. [Source inventory](verification/sources.tsv) · [Notice](NOTICE) · [License](LICENSE)

Jaehun Jung directed the research. OpenAI Codex developed the additional arguments, constructed the witnesses, ran the computations and Lean checks, and drafted the paper and its reproducibility materials.
