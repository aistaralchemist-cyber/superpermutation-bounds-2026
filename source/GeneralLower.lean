import CollisionExamples
import SmallBranch

/-! The same numerical lower function used by the calculator, including its small branch. -/
namespace GeneralAlt.Uniform
open SuperpermutationLowerBound.ChainReturns

noncomputable def baseline (n : ℕ) : ℕ :=
  if n < 8 then SmallGeneralBaseline.lower n else publishedBaseline n

theorem baseline_valid : ValidLower baseline := by
  intro n w hw
  unfold baseline
  split
  · exact SmallGeneralBaseline.covers_lower n w hw
  · exact publishedBaseline_valid n w hw

noncomputable def lower (n : ℕ) : ℕ :=
  let m := (n - 1) / 3
  if n = 3 * m + 1 ∧ 3 ≤ m then
    max (baseline n) (max
      (bound n (tightP m (publicReturn m)) (tightT m (publicReturn m)))
      (bound n (tightP m (CollisionFormula.cutoff m)) (tightT m (CollisionFormula.cutoff m))))
  else baseline n

theorem word_lower : ValidLower lower := by
  intro n w hw
  let m := (n - 1) / 3
  unfold lower
  change (if n = 3 * m + 1 ∧ 3 ≤ m then _ else _) ≤ _
  split
  next h =>
    obtain ⟨he,hm⟩ := h
    generalize hj : m = j at he hm ⊢
    subst n
    have hr : (3 * j + 1 - 1) / 3 = j := by omega
    simp only [hr]
    exact max_le (baseline_valid _ w hw)
      (max_le (word_general j hm w hw) (CollisionFormula.covering_lower j hm w hw))
  next => exact baseline_valid n w hw

/-- Closed-form choice using the three certified early collisions. -/
def explicitReturn (m : ℕ) : ℕ :=
  if m = 3 ∨ m = 4 then 3 else if m = 5 then 7 else publicReturn m

theorem explicit_valid (m : ℕ) (hm : 3 ≤ m) :
    1 ≤ explicitReturn m ∧ Both m (explicitReturn m) := by
  by_cases h3 : m = 3
  · subst m
    exact ⟨by decide, CollisionFormula.both_of_hits 3 3 (by decide) CollisionFormula.hits10⟩
  by_cases h4 : m = 4
  · subst m
    exact ⟨by decide, CollisionFormula.both_of_hits 4 3 (by decide) CollisionFormula.hits13⟩
  by_cases h5 : m = 5
  · subst m
    exact ⟨by decide, CollisionFormula.both_of_hits 5 7 (by decide) CollisionFormula.hits16⟩
  simp only [explicitReturn, h3, h4, h5, or_self, ite_false]
  exact ⟨SuperpermutationBounds.ChainReturns.returnZero_pos (by omega), public_both m hm⟩

noncomputable def closedLower (n : ℕ) : ℕ :=
  let m := (n - 1) / 3
  if n = 3 * m + 1 ∧ 3 ≤ m then
    max (baseline n) (max
      (bound n (tightP m (publicReturn m)) (tightT m (publicReturn m)))
      (bound n (tightP m (explicitReturn m)) (tightT m (explicitReturn m))))
  else baseline n

theorem closed_word_lower : ValidLower closedLower := by
  intro n w hw
  let m := (n - 1) / 3
  unfold closedLower
  change (if n = 3 * m + 1 ∧ 3 ≤ m then _ else _) ≤ _
  split
  next h =>
    obtain ⟨he,hm⟩ := h
    generalize hj : m = j at he hm ⊢
    subst n
    have hr : (3 * j + 1 - 1) / 3 = j := by omega
    simp only [hr]
    obtain ⟨hp,hc⟩ := explicit_valid j hm
    exact max_le (baseline_valid _ w hw)
      (max_le (word_general j hm w hw) (tight_word hm hp hc w hw))
  next => exact baseline_valid n w hw

#print axioms word_lower
#print axioms closed_word_lower
end GeneralAlt.Uniform
