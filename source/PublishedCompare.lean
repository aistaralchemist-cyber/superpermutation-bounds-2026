module
public import StrictCompare
public import bridge.FrozenParameters
public import bridge.Normalization
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

/-- Compare directly to the original exact-parameter manuscript table,
including its outer natural-number ceiling, on the actual word problem. -/
theorem published_plus_four (m : ℕ) (hm : 5 ≤ m) (w : List (Fin (3*m+1)))
    (hw : SuperpermutationBounds.Covers w) :
    paperBound (3*m+1) (exactParameters (3*m+1)).1 (exactParameters (3*m+1)).2 + 4 ≤ w.length := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 3*m+1) (exactParameters_admissible (by omega))]
  have hp : exactParameters (3*m+1) =
      (priceP m (publicReturn m), priceT m (publicReturn m)) := by
    rw [exactParameters_large (by omega)]
    simp [generalParameters, priceP, priceT, publicReturn]
  rw [hp]
  exact (public_strict m hm).trans (word_general m (by omega) w hw)

#print axioms published_plus_four
end GeneralAlt
