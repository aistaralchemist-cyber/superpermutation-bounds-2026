-- The first two bridge lemmas are from Pantone's adapter as retained in Halfar's B-51.
-- Adapted 25 November 2026 to state the coefficient-86 result.
import AlmanacDefs
import Upper86

namespace JungAdapter
/-- The Almanac's factorial is `Nat.factorial`. -/
theorem fact_eq (k : Nat) : Almanac.fact k = Nat.factorial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Almanac.fact, Nat.factorial, ih]

/-- The project's covering predicate is the Almanac's superpermutation predicate. -/
theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hp hl
    obtain ⟨u, v, huv⟩ := h p hl hp
    exact ⟨u, v, huv.symm⟩
  · intro h p hl hp
    obtain ⟨u, v, huv⟩ := h p hp hl
    exact ⟨u, v, huv.symm⟩

def ExplicitErrorLog20_86 : Prop :=
  ∀ n : Nat, 2904 * 10400 ^ 2 * 6 ^ 20 * 4 ^ 2 ≤ n →
    (∃ w : Almanac.Word n, Almanac.IsSuperpermutation n w ∧
      (w.length : Real) ≤ (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) +
        86 * (Almanac.fact (n - 4) : Real) * Real.log n ^ (1 / 10 : Real) *
          (n : Real) ^ (-1 / 20 : Real)) ∧
    ∀ w : Almanac.Word n, Almanac.IsSuperpermutation n w →
      (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) -
        86 * (Almanac.fact (n - 4) : Real) * Real.log n ^ (1 / 10 : Real) *
          (n : Real) ^ (-1 / 20 : Real) ≤ (w.length : Real)

open CoefficientTwoPrecision.Asym22

theorem checked : ExplicitErrorLog20_86 := by
  intro n hn
  rw [← logThreshold_six] at hn
  simp only [fact_eq]
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  constructor
  · obtain ⟨w,hw,h⟩ := word_rate86 n hn
    refine ⟨w, (covers_iff w).mp hw, ?_⟩
    rw [hF3] at h
    linarith only [h]
  · intro w hw
    have hmin : (ConstAsym.L n : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast ConstAsym.L_le_length ((covers_iff w).mpr hw)
    have hl := (abs_le.mp (shortest_rate86 n hn)).1
    rw [hF3] at hl
    linarith only [hl, hmin]

end JungAdapter
