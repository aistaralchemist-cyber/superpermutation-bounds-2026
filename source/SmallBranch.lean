import Hunter.Paper
import Superperm.Bridge
import LowerBounds.TheoremBCore
import LowerBounds.DeficitOne
import LowerBounds.LemmaZ

/-! Small-alphabet specializations of the published general lower inequalities. -/
namespace SmallGeneralBaseline

open SuperpermutationBounds SuperpermLowerBounds

/-- For all other alphabet sizes this branch is zero. -/
def lower : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 9
  | 4 => 33
  | 5 => 153
  | 6 => 870
  | 7 => 5895
  | _ => 0

private theorem one (w : List (Fin 1)) (hw : Covers w) : 1 ≤ w.length := by
  obtain ⟨left,right,he⟩ := hw [0] (by decide) (by decide)
  rw [he]
  simp
  omega

private theorem two (w : List (Fin 2)) (hw : Covers w) : 3 ≤ w.length := by
  obtain ⟨a,b,hab⟩ := hw [0,1] (by decide) (by decide)
  obtain ⟨c,d,hcd⟩ := hw [1,0] (by decide) (by decide)
  by_contra! h
  have h₁ := congrArg List.length hab
  have h₂ := congrArg List.length hcd
  simp at h₁ h₂
  have ha : a = [] := List.length_eq_zero_iff.mp (by omega)
  have hb : b = [] := List.length_eq_zero_iff.mp (by omega)
  have hc : c = [] := List.length_eq_zero_iff.mp (by omega)
  have hd : d = [] := List.length_eq_zero_iff.mp (by omega)
  have hne : ([0,1] : List (Fin 2)) ≠ [1,0] := by decide
  exact hne (by simpa [ha,hb,hc,hd] using hab.symm.trans hcd)

/-- The bound /b/9 at seven. Both geometric hypotheses of Theorem B are discharged. -/
theorem seven (w : List (Fin 7)) (hw : Covers w) : 5895 ≤ w.length := by
  have g : G5Statement 7 := by
    intro p hp chain gaps partials hpart
    exact partition_unit_after_full_next_large (by decide) hp hpart
  have z : ZStatement 7 := by
    intro p hp hk hr s he hz hμ
    exact lemma_Z (by decide) hp hr s he hz hμ
  have h7 := superperm_boundB_of (k := 7) (by decide) g z
  have val : boundB 7 = 5895 := by decide
  rw [val] at h7
  exact (SuperpermBridge.hunter_le_ssuper_iff (by decide : 0 < 7)).mp h7 w hw

/-- An unconditional word-level table for the small branch of the general formula. -/
theorem covers_lower (n : ℕ) (w : List (Fin n)) (hw : Covers w) : lower n ≤ w.length := by
  match n with
  | 0 => exact Nat.zero_le _
  | 1 => exact one w hw
  | 2 => exact two w hw
  | 3 =>
    exact (SuperpermBridge.hunter_le_ssuper_iff (by decide : 0 < 3)).mp
      Hunter.Paper.pointwise_3 w hw
  | 4 =>
    exact (SuperpermBridge.hunter_le_ssuper_iff (by decide : 0 < 4)).mp
      Hunter.Paper.pointwise_4 w hw
  | 5 =>
    exact (SuperpermBridge.hunter_le_ssuper_iff (by decide : 0 < 5)).mp
      superperm_kisic_numerical_bounds.1 w hw
  | 6 =>
    exact (SuperpermBridge.hunter_le_ssuper_iff (by decide : 0 < 6)).mp
      superperm_kisic_numerical_bounds.2.1 w hw
  | 7 => exact seven w hw
  | n+8 => exact Nat.zero_le _

#print axioms seven
#print axioms covers_lower

end SmallGeneralBaseline
