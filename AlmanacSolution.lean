import AlmanacDefs
import JungComparison

namespace AlmanacSubmission

/-- Every contiguous-covering word obeys the explicit piecewise chain bound.
On the residue class n = 3m + 1, m ≥ 5, the numerical bound gains at least four
letters over Pantone's published general lower formula. -/
theorem alternating_chain_lower :
    (∀ n (w : Almanac.Word n), Almanac.IsSuperpermutation n w →
      GeneralAlt.Uniform.closedLower n ≤ w.length) ∧
    (∀ m : Nat, 5 ≤ m → GeneralAlt.publishedBaseline (3*m+1) + 4 ≤
      GeneralAlt.Uniform.closedLower (3*m+1)) := by
  have cover {n} (w : Almanac.Word n) (hw : Almanac.IsSuperpermutation n w) :
      SuperpermutationBounds.Covers w := by
    intro p hl hp
    obtain ⟨u, v, huv⟩ := hw p hp hl
    exact ⟨u, v, huv.symm⟩
  constructor
  · exact fun n w hw => GeneralAlt.Uniform.closed_word_lower n w (cover w hw)
  · exact GeneralAlt.Uniform.closed_gain_four

end AlmanacSubmission
