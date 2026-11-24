module

public import alternation.AlternatingFactors
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

/-! Parameterize the cut-count payment of Pantone's frozen Lean development by
an arbitrary positive binary-run cap L. This also covers odd caps. -/
theorem allowance_of_count {b L : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ L) (ls : List ℕ) (hq : 3 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (hcuts : ls.length - 2 ≤ ordinaryBadCount b ls + oneCount ls +
      L * (ordinaryBadCount b ls + 3 * oneCount ls + excessWitness b ls + 1)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (2 * (L : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / ((L : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  have hp := weighted_defect_payment hb ls hbound htrap
  have hmass := sum_add_chain_deficits b ls (by intro x hx; exact (hbound x hx).2)
  have hbR : (1 + L) * ordinaryBadCount b ls ≤
      2 * L * ordinaryBadCount b ls := by nlinarith
  have hwR : (1 + 3 * L) * oneCount ls ≤
      2 * L * (b - 3) * oneCount ls := by
    have hb3 : 2 ≤ b - 3 := by omega
    have hcoeff : 1 + 3 * L ≤ 2 * L * (b - 3) := by nlinarith
    exact Nat.mul_le_mul_right _ hcoeff
  have hpaid : ls.length - 2 ≤
      L * (2 * lossMass b ls - (ls.length - 3) + 1) := by
    have hsub : 2 * ordinaryBadCount b ls + 2 * (b - 3) * oneCount ls +
        excessWitness b ls ≤ 2 * lossMass b ls - (ls.length - 3) := by omega
    have hweighted := Nat.mul_le_mul_left (L) hsub
    nlinarith
  have hdef : ls.length - 3 ≤ 2 * lossMass b ls := by omega
  have hpoly : ls.length + L * ls.length ≤ 2 * L * lossMass b ls + 4 * L + 2 := by
    have hq2 : ls.length - 2 + 2 = ls.length := Nat.sub_add_cancel (by omega)
    have hq3 : ls.length - 3 + 3 = ls.length := Nat.sub_add_cancel hq
    have hd := Nat.sub_add_cancel hdef
    have hq3R := congrArg (fun v => L * v) hq3
    have hdR := congrArg (fun v => L * v) hd
    nlinarith
  have hpaidQ : (ls.length : ℚ) + (L : ℚ) * ls.length ≤
      2 * (L : ℚ) * lossMass b ls + 4 * (L : ℚ) + 2 := by
    exact_mod_cast hpoly
  have hmassQ : (ls.sum : ℚ) + (lossMass b ls : ℚ) = (b : ℚ) * ls.length := by
    exact_mod_cast hmass
  have hRQ : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
  have hscaled : (1 / (2 * (L : ℚ))) * (ls.length : ℚ) + (ls.length : ℚ) / 2 ≤
      lossMass b ls + 2 + 2 * (1 / (2 * (L : ℚ))) := by
    calc
      _ = (1 / (2 * (L : ℚ))) *
          ((ls.length : ℚ) + (L : ℚ) * ls.length) := by
        field_simp [ne_of_gt hRQ]
      _ ≤ (1 / (2 * (L : ℚ))) *
          (2 * (L : ℚ) * lossMass b ls + 4 * (L : ℚ) + 2) := by
        exact mul_le_mul_of_nonneg_left hpaidQ (by positivity)
      _ = _ := by
        field_simp [ne_of_gt hRQ]
        ring
  have hhalf : 1 / ((L : ℚ)) = 2 * (1 / (2 * (L : ℚ))) := by
    field_simp [ne_of_gt hRQ]
  rw [hhalf]
  nlinarith

theorem interior_count {b L : ℕ} (hb : 1 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (L) (interiorLosses b ls)) :
    ls.length - 2 ≤ ordinaryBadCount b ls + oneCount ls +
      L * (ordinaryBadCount b ls + 3 * oneCount ls + excessWitness b ls + 1) := by
  have hc := binary_string_count_uniform (interiorLosses b ls) halt
  rw [interiorLosses_length,
    interiorLosses_cuts hb ls (fun x hx => (hbound x hx).2)] at hc
  have hbnd := interiorLosses_removed b ls
  have hcuts := equal_cuts_paid hb ls hbound htrap
  have hremoved := Nat.mul_le_mul_left (L) hbnd
  have hpaid := Nat.mul_le_mul_left (L) hcuts
  nlinarith

theorem allowance_of_bounded {b L : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ L) (ls : List ℕ) (hq : 3 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (L) (interiorLosses b ls)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (2 * (L : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / ((L : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) :=
  allowance_of_count hb hR ls hq hbound htrap
    (interior_count (by omega) ls hbound htrap halt)

theorem allowance_two {b L : ℕ} (hR : 1 ≤ L) (ls : List ℕ)
    (hq : ls.length = 2) (hbound : ∀ x ∈ ls, x ≤ b) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (2 * (L : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / ((L : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  have hmass := sum_add_chain_deficits b ls hbound
  rw [hq] at hmass
  have hs : ls.sum ≤ 2 * b := by omega
  have hsQ : (ls.sum : ℚ) ≤ 2 * (b : ℚ) := by exact_mod_cast hs
  have hRQ : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
  have hhalf : 1 / ((L : ℚ)) = 2 * (1 / (2 * (L : ℚ))) := by
    field_simp [ne_of_gt hRQ]
  rw [hq, hhalf]
  norm_num at hsQ ⊢
  linarith

theorem allowance {b L : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ L) (ls : List ℕ) (hq : 2 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (L) (interiorLosses b ls)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (2 * (L : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / ((L : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  by_cases hthree : 3 ≤ ls.length
  · exact allowance_of_bounded hb hR ls hthree hbound htrap halt
  · exact allowance_two hR ls (by omega) (fun x hx => (hbound x hx).2)

end GeneralAlt
