# Superpermutation bounds

**Jaehun Jung** · Independent Researcher, Republic of Korea · 25 November 2026

Let S(n) be the minimum length of a word containing all n! permutations of n symbols as consecutive substrings. This collection contains three research preprints covering a general upper bound, a general lower bound and a constructed word.

## An explicit error coefficient of 86 for superpermutation length

For all integers n ≥ 2904·10400²·6²⁰·4², the absolute error from n! + (n−1)! + (n−2)! + 2(n−4)! is at most 86(n−4)!(ln n)^(1/10)n^(−1/20). This sharpens the explicit constant 214 in Jakub Halfar's bound at the same threshold and exponents. [Paper](general-upper.pdf) · [LaTeX](general-upper.tex) · [Lean project](https://github.com/aistaralchemist-cyber/superpermutation-bounds-2026/tree/codex/general-upper) · [Halfar's bound](https://superpermutations.com/b/51)

## A shorter superpermutation on fourteen symbols

Reordering 552 pieces of Jakub Halfar's W-0165 saves 627 characters and yields a word of length **93,904,707,285**. Direct scanning found all **87,178,291,200** permutations. The proof, program, compressed word and 154 scattered-window witnesses accompany the paper. The separate, previously accepted lower bound **93,891,141,157** gives an interval of width **13,566,128**. The new word was submitted to the Almanac as W-0166. [Paper](fourteen-symbol-word.pdf) · [LaTeX](fourteen-symbol-word.tex) · [Submitted word](W-0166.detour) · [Verification supplement](fourteen-symbol-verification.zip) · [Source W-0165](https://superpermutations.com/w/W-0165) · [Previously accepted lower bound](https://superpermutations.com/b/52)

## Interior alternating chains and lower bounds for superpermutations

The inequality improves the previous general formula by at least four letters for every alphabet size congruent to one modulo three from sixteen onward. Through fourteen symbols, every individual record is at least as strong. The ten- and thirteen-symbol evaluations illustrate the general result. [Paper](general-lower.pdf) · [LaTeX](general-lower.tex) · [Lean project](https://github.com/aistaralchemist-cyber/superpermutation-bounds-2026/tree/codex/general-lower) · [Calculations and Lean sources](https://github.com/aistaralchemist-cyber/superpermutation-bounds-2026/archive/refs/heads/codex/general-lower.zip)

## Authorship and reuse

Jaehun Jung directed the research. OpenAI Codex developed the additional arguments, implemented and ran computations and formalizations, and drafted the manuscripts under his direction. The papers and supplements credit the underlying results and constructions. Halfar's source word and its adaptation carry the Almanac's CC BY 4.0 license. Each verification package includes the applicable source notices. These are author-posted research manuscripts.
