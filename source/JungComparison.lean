import GeneralValues

namespace GeneralAlt.Uniform
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

/-- The gain belongs to the numerical expression itself. -/
theorem closed_gain_four (m : ℕ) (hm : 5 ≤ m) :
    publishedBaseline (3 * m + 1) + 4 ≤ closedLower (3 * m + 1) := by
  have hn : 8 ≤ 3 * m + 1 := by omega
  have hr : (3 * m + 1 - 1) / 3 = m := by omega
  unfold closedLower
  simp only [hr, show 3 ≤ m by omega, and_self, ite_true]
  apply (le_max_of_le_right (le_max_of_le_left ?_))
  unfold publishedBaseline
  rw [if_pos hn, ← bound_eq_paperBound hn (exactParameters_admissible hn)]
  have hp : exactParameters (3 * m + 1) =
      (priceP m (publicReturn m), priceT m (publicReturn m)) := by
    rw [exactParameters_large (by omega)]
    simp [generalParameters, priceP, priceT, publicReturn]
  rw [hp]
  exact public_strict m hm

end GeneralAlt.Uniform
