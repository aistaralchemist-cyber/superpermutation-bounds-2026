# An explicit error coefficient of 86 for superpermutation length

Jaehun Jung · Independent Researcher, Republic of Korea · 25 November 2026

For every integer $n\ge 2904\cdot10400^2\cdot6^{20}\cdot4^2$, put $A(n)=n!+(n-1)!+(n-2)!+2(n-4)!$. The shortest superpermutation length satisfies

$$
|S(n)-A(n)| \le 86(n-4)!(\log n)^{1/10}n^{-1/20}.
$$

The same result supplies an actual word within the upper endpoint. Halfar's estimate has coefficient 214 at the same threshold and exponent. Using every admissible integer parameter in his finite construction gives 86. At the last integer before parameter 7 is admissible, the coefficient required by the numerical construction guarantee lies strictly between 85 and 86. Proposition 3 in the manuscript specifies the scope of this obstruction. [Manuscript](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Halfar's listed estimate](https://superpermutations.com/b/51)

## Lean verification

The Almanac batch exports one custom theorem, `AlmanacSubmission.explicit_error_log20_86`. Its proposition quantifies over alphabet sizes and over words in the Almanac's own definitions. It gives the covering word for the upper endpoint and the universal lower inequality for the other endpoint. [Almanac solution](AlmanacSolution.lean) · [Statement and adapter](JungAdapter.lean) · [Proof](Upper86.lean)

Lean 4.35.0 and the Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned. From the repository root run

~~~sh
lake exe cache get
lake build AlmanacSolution
lake env leanchecker -v Upper86 JungAdapter AlmanacSolution
~~~

The local build reported `propext`, `Classical.choice`, and `Quot.sound` for the submitted theorem. The new modules also passed kernel replay against their imports. [Build log](verification/build.log) · [Replay log](verification/leanchecker.log)

## Provenance

The `lean/` and `licenses/` trees come from the exact Halfar revision used to certify Almanac bound 51. `Upper86.lean` is the additional estimate. `JungAdapter.lean` reuses the two vocabulary lemmas from Pantone's adapter as retained by Halfar. Jaehun Jung directed the research. OpenAI Codex developed the additional mathematical argument and proof and drafted the manuscript. [Halfar's snapshot](https://github.com/jhalfar/superpermutation-almanac-lean/tree/4392df9764a5be7e5bd4dc15a414defe94077eaf) · [License](LICENSE) · [Attribution](NOTICE)
