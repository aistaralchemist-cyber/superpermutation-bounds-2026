module

public import AltBound
public import CutPayment
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

def tightP (m R : ℕ) : ℚ := 2*(m:ℚ)+1/2+1/(2*((2*R-1 : ℕ):ℚ))
def tightT (m R : ℕ) : ℚ := 4*(m:ℚ)-3-1/((2*R-1 : ℕ):ℚ)

def HasInteriorCut (m R : ℕ) : Prop :=
  ∀ {hk : 7 ≤ 3*m+1} {P : OverlapPath (3*m+1)} {hP : IsBlockAligned P}
    (s : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (_ : RealizesChains (3*m-2) ls s.deficitString),
    (∀ x ∈ ls, x ≤ 2*m-1) → BoundedAlternation (2*R-1) (interiorLosses (2*m-1) ls)

theorem tight_admissible {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) :
    SuperpermutationLowerBound.ChainReturns.Admissible (3*m+1-1) (tightP m R) (tightT m R) := by
  let L := 2*R-1
  have hLm : 1 ≤ L := by dsimp [L]; omega
  have hl : (1:ℚ) ≤ L := by exact_mod_cast hLm
  have hq : (3:ℚ) ≤ m := by exact_mod_cast hm
  have hpos : (0:ℚ) < L := by linarith
  have hinv : 1/(L:ℚ) ≤ 1 := (div_le_one hpos).2 hl
  have hhalf : 1/(2*(L:ℚ)) = (1/(L:ℚ))/2 := by ring
  have hr : (0:ℚ) ≤ 1/(L:ℚ) := by positivity
  unfold tightP tightT
  change SuperpermutationLowerBound.ChainReturns.Admissible (3*m+1-1)
    (2*(m:ℚ)+1/2+1/(2*(L:ℚ))) (4*(m:ℚ)-3-1/(L:ℚ))
  rw [hhalf]
  constructor
  · omega
  · linarith
  · linarith
  · linarith
  · rw [show 3*m+1-1=3*m by omega]
    push_cast
    have hmult := mul_nonneg (show 0 ≤ 3*(m:ℚ)-4 by linarith)
      (show 0 ≤ 1-1/(L:ℚ) by linarith)
    nlinarith [mul_nonneg (show 0 ≤ (m:ℚ) by linarith) (show 0 ≤ (m:ℚ)-3 by linarith)]

theorem tight_chain_sum {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : HasInteriorCut m R)
    {hk : 7 ≤ 3*m+1} {P : OverlapPath (3*m+1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (hreal : RealizesChains (3*m-2) ls segment.deficitString)
    (hne : ls ≠ []) (hpos : ∀ x ∈ ls, 1 ≤ x) :
    2 * (ls.sum : ℚ) ≤ 2 * tightP m R + tightT m R * ((ls.length : ℚ)-1) := by
  have H := actual_segment_returnAvoidance (by omega : 7 ≤ 3*m) segment
  have hp : period (3*m) = 2*m := by simp [period]
  have hpbound := chain_bound_of_pure hreal H.basic.pure
  rw [hp] at hpbound
  by_cases hq : 2 ≤ ls.length
  · have hb := chain_bound_of_basic (by rw [hp]; omega) hreal hpos H.basic hq
    rw [hp] at hb
    have ht := fourChainTrap_of_universal hreal (H.residueZero (by omega))
    rw [hp] at ht
    have halt := h segment hreal hb
    have hs := allowance (b:=2*m-1) (L:=2*R-1) (by omega) (by omega) ls hq
      (fun x hx => ⟨hpos x hx,hb x hx⟩) ht halt
    have hbcast : ((2*m-1 : ℕ) : ℚ) = 2*(m:ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*m)]
      push_cast
      rfl
    rw [hbcast] at hs
    unfold tightP tightT
    linarith
  · have hlen : ls.length=1 := by
      have := List.length_pos_iff.mpr hne
      omega
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hlen
    have hx : (x:ℚ) ≤ 2*(m:ℚ) := by exact_mod_cast hpbound x (by simp)
    have hr' : (0:ℚ) ≤ 1/(2*((2*R-1 : ℕ):ℚ)) := by positivity
    simp only [List.sum_singleton, List.length_singleton, Nat.cast_one, sub_self,
      mul_zero, add_zero, tightP]
    linarith

theorem tight_packing {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : HasInteriorCut m R) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3*m+1) (by omega)
      (tightP m R) (tightT m R) := by
  intro P hP segment
  change ChainPacking (3*m-2) (tightP m R) (tightT m R) segment.deficitString
  intro gaps hg before after hd
  have hreal := realizes_chainLengths (by omega : 3 ≤ 3*m-2) hg hd
  have hs := tight_chain_sum hm hR h segment hreal
    (chainLengthsFrom_nonempty (3*m-2) 1 gaps) (chainLengths_positive (3*m-2) gaps)
  rw [chainLengths_sum,chainLengths_length] at hs
  push_cast at hs
  linarith

theorem tight_word_of_cut {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : HasInteriorCut m R)
    (w : List (Fin (3*m+1))) (hw : SuperpermutationBounds.Covers w) :
    SuperpermutationLowerBound.ChainReturns.bound (3*m+1) (tightP m R) (tightT m R) ≤ w.length :=
  SuperpermutationLowerBound.ChainReturns.word_bound_of_actualPacking (by omega)
    (tight_admissible hm hR) (tight_packing hm hR h) w hw


end GeneralAlt
