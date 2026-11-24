import AllSizes
import bridge.FrozenBounds

namespace GeneralAlt
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns

/-- The exact-return table starts at eight. Below eight we retain the
elementary alphabet bound; any certified stronger input can be combined. -/
noncomputable def publishedBaseline (n : ℕ) : ℕ :=
  if 8≤n then paperBound n (exactParameters n).1 (exactParameters n).2 else n

theorem publishedBaseline_valid : ValidLower publishedBaseline := by
  intro n w hw
  unfold publishedBaseline
  split
  next h => exact exact_word_bound n h w hw
  next => exact alphabet_lower n w hw

noncomputable def publishedCombined := combinedLower publishedBaseline

theorem all_sizes_published : ValidLower publishedCombined := all_sizes publishedBaseline_valid

#print axioms all_sizes_published
end GeneralAlt
