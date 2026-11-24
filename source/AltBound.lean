module

public import alternation.AlternatingFactors
public import SuperpermutationLowerBound.Refinement.GeometryPacking
public import bridge.GenericTransfer

@[expose] public section

namespace GeneralAlt
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

/-- Both orientations of the extremal pair are excluded from every actual segment. -/
def Both (m R : ℕ) : Prop :=
  ∀ {hk : 7 ≤ 3*m+1} {P : OverlapPath (3*m+1)} {hP : IsBlockAligned P}
    (s : BlockAlignedLightSegment hk P hP),
    (¬ CellFactor (3*m-2) (repeatedCells (completedPair (2*m-1) (2*m-2)) R) s.deficitString) ∧
    (¬ CellFactor (3*m-2) (repeatedCells (completedPair (2*m-2) (2*m-1)) R) s.deficitString)

def priceP (m R : ℕ) : ℚ := 2*(m:ℚ)+1/2+1/(4*(R:ℚ))
def priceT (m R : ℕ) : ℚ := 4*(m:ℚ)-3-1/(2*(R:ℚ))

theorem chain_sum {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : Both m R)
    {hk : 7 ≤ 3*m+1} {P : OverlapPath (3*m+1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (hreal : RealizesChains (3*m-2) ls segment.deficitString)
    (hne : ls ≠ []) (hpos : ∀ x ∈ ls, 1 ≤ x) :
    2 * (ls.sum : ℚ) ≤ 2 * priceP m R + priceT m R * ((ls.length : ℚ)-1) := by
  have H := actual_segment_returnAvoidance (by omega : 7 ≤ 3*m) segment
  have hp : period (3*m) = 2*m := by simp [period]
  have hpbound := chain_bound_of_pure hreal H.basic.pure
  rw [hp] at hpbound
  by_cases hq : 2 ≤ ls.length
  · have hb := chain_bound_of_basic (by rw [hp]; omega) hreal hpos H.basic hq
    rw [hp] at hb
    have ht := fourChainTrap_of_universal hreal (H.residueZero (by omega))
    rw [hp] at ht
    obtain ⟨h1,h2⟩ := h segment
    have ha : NoAlternatingFactor (2*m-1) R ls := by
      apply no_alternatingFactor_of_periodic_avoidance hreal
      · simpa only [show 2*m-1-1 = 2*m-2 by omega] using h1
      · simpa only [show 2*m-1-1 = 2*m-2 by omega] using h2
    have halt := (boundedAlternation_of_no_factor (2*m-1) R ls hb ha).interior
    have hs := alternation_allowance_nontrivial (b:=2*m-1) (by omega) hR ls hq
      (fun x hx => ⟨hpos x hx,hb x hx⟩) ht halt
    have hbcast : ((2*m-1 : ℕ) : ℚ) = 2*(m:ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*m)]
      push_cast
      rfl
    rw [hbcast] at hs
    unfold priceP priceT
    linarith
  · have hlen : ls.length=1 := by
      have := List.length_pos_iff.mpr hne
      omega
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hlen
    have hx : (x:ℚ) ≤ 2*(m:ℚ) := by exact_mod_cast hpbound x (by simp)
    have hr' : (0:ℚ) ≤ 1/(4*(R:ℚ)) := by positivity
    simp only [List.sum_singleton, List.length_singleton, Nat.cast_one, sub_self,
      mul_zero, add_zero, priceP]
    linarith

theorem packing {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : Both m R) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3*m+1) (by omega)
      (priceP m R) (priceT m R) := by
  intro P hP segment
  change ChainPacking (3*m-2) (priceP m R) (priceT m R) segment.deficitString
  intro gaps hg before after hd
  have hreal := realizes_chainLengths (by omega : 3 ≤ 3*m-2) hg hd
  have hs := chain_sum hm hR h segment hreal
    (chainLengthsFrom_nonempty (3*m-2) 1 gaps) (chainLengths_positive (3*m-2) gaps)
  rw [chainLengths_sum,chainLengths_length] at hs
  push_cast at hs
  linarith

theorem word_bound {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : Both m R)
    (had : SuperpermutationLowerBound.ChainReturns.Admissible (3*m+1-1) (priceP m R) (priceT m R))
    (w : List (Fin (3*m+1))) (hw : SuperpermutationBounds.Covers w) :
    SuperpermutationLowerBound.ChainReturns.bound (3*m+1) (priceP m R) (priceT m R) ≤ w.length :=
  SuperpermutationLowerBound.ChainReturns.word_bound_of_actualPacking (by omega)
    had (packing hm hR h) w hw

open SuperpermutationLowerBound.ChainReturns in
theorem word13 (h : Both 4 3) (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) :
    6746626661 ≤ w.length := by
  have hA : Admissible (3*4+1-1) (priceP 4 3) (priceT 4 3) := by
    constructor <;> norm_num [priceP,priceT]
  have he : bound (3*4+1) (priceP 4 3) (priceT 4 3) = 6746626661 := by
    have hz : ⌈(181541605450/4471 : ℚ)⌉₊ = 40604251 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
    norm_num [bound,lam,intercept,priceP,priceT,Nat.factorial]
    rw [hz]
  exact he ▸ word_bound (m:=4) (R:=3) (by decide) (by decide) h hA w hw

open SuperpermutationLowerBound.ChainReturns in
theorem word16 (h : Both 5 7) (w : List (Fin 16)) (hw : SuperpermutationBounds.Covers w) :
    22318554321226 ≤ w.length := by
  have hA : Admissible (3*5+1-1) (priceP 5 7) (priceT 5 7) := by
    constructor <;> norm_num [priceP,priceT]
  have he : bound (3*5+1) (priceP 5 7) (priceT 5 7) = 22318554321226 := by
    have hz : ⌈(3992329845496774/45321 : ℚ)⌉₊ = 88090065213 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
    norm_num [bound,lam,intercept,priceP,priceT,Nat.factorial]
    rw [hz]
  exact he ▸ word_bound (m:=5) (R:=7) (by decide) (by decide) h hA w hw

#print axioms word13
#print axioms word16
end GeneralAlt
