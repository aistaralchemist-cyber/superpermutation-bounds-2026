import CollisionFormula

namespace GeneralAlt.CollisionFormula
open SuperpermutationLowerBound.ChainReturns
set_option maxRecDepth 180000
set_option maxHeartbeats 12000000

/-- Each orientation gives a pair of (cell, row, slot) coordinates. -/
theorem hits10 : pairHits 3 3 := by
  constructor
  · refine ⟨(⟨4, by decide⟩, 0, 0), (⟨18, by decide⟩, 0, 1), ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  · refine ⟨(⟨8, by decide⟩, 0, 0), (⟨22, by decide⟩, 0, 1), ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cutoff10 : cutoff 3 ≤ 3 := cutoff_le_of_hits 3 2 (by decide) hits10

theorem computed_bound10 :
    4033375 ≤ bound 10 (tightP 3 (cutoff 3)) (tightT 3 (cutoff 3)) := by
  have h₁ := (cutoff_spec 3 (by decide)).1
  have h₂ := cutoff10
  generalize cutoff 3 = r at h₁ h₂ ⊢
  interval_cases r <;> decide +kernel

theorem word10 (w : List (Fin 10)) (hw : SuperpermutationBounds.Covers w) : 4033375 ≤ w.length :=
  computed_bound10.trans (covering_lower 3 (by decide) w hw)

#print axioms word10
theorem hits13 : pairHits 4 3 := by
  constructor
  · refine ⟨(⟨0, by decide⟩, 0, 8), (⟨32, by decide⟩, 0, 0), ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  · refine ⟨(⟨6, by decide⟩, 0, 8), (⟨38, by decide⟩, 0, 0), ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cutoff13 : cutoff 4 ≤ 3 := cutoff_le_of_hits 4 2 (by decide) hits13

theorem computed_bound13 :
    6746626690 ≤ bound 13 (tightP 4 (cutoff 4)) (tightT 4 (cutoff 4)) := by
  have h₁ := (cutoff_spec 4 (by decide)).1
  have h₂ := cutoff13
  generalize cutoff 4 = r at h₁ h₂ ⊢
  interval_cases r <;> decide +kernel

theorem word13 (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) : 6746626690 ≤ w.length :=
  computed_bound13.trans (covering_lower 4 (by decide) w hw)

#print axioms word13
theorem hits16 : pairHits 5 7 := by
  constructor
  · refine ⟨(⟨0, by decide⟩, 11, 11), (⟨109, by decide⟩, 2, 0), ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  · refine ⟨(⟨8, by decide⟩, 11, 11), (⟨117, by decide⟩, 2, 0), ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cutoff16 : cutoff 5 ≤ 7 := cutoff_le_of_hits 5 6 (by decide) hits16

theorem computed_bound16 :
    22318554323969 ≤ bound 16 (tightP 5 (cutoff 5)) (tightT 5 (cutoff 5)) := by
  have h₁ := (cutoff_spec 5 (by decide)).1
  have h₂ := cutoff16
  generalize cutoff 5 = r at h₁ h₂ ⊢
  interval_cases r <;> decide +kernel

theorem word16 (w : List (Fin 16)) (hw : SuperpermutationBounds.Covers w) : 22318554323969 ≤ w.length :=
  computed_bound16.trans (covering_lower 5 (by decide) w hw)

#print axioms word16
end GeneralAlt.CollisionFormula
