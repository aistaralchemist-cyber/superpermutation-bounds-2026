module

public import InteriorCut
public import TightMain
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

theorem tight_word {m R : ℕ} (hm : 3 ≤ m) (hR : 1 ≤ R) (h : Both m R)
    (w : List (Fin (3*m+1))) (hw : SuperpermutationBounds.Covers w) :
    SuperpermutationLowerBound.ChainReturns.bound (3*m+1) (tightP m R) (tightT m R) ≤ w.length := by
  apply tight_word_of_cut hm hR _ w hw
  intro hk P hP s ls hreal hb
  obtain ⟨hx,hy⟩ := h s
  apply interiorCut hR (by omega) hb hreal
  · simpa only [show 2*m-1-1 = 2*m-2 by omega] using hx
  · simpa only [show 2*m-1-1 = 2*m-2 by omega] using hy

open SuperpermutationLowerBound.ChainReturns in
theorem tight13 (h : Both 4 3) (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) :
    6746626690 ≤ w.length := by
  have hz : ⌈(75442751605/1858 : ℚ)⌉₊ = 40604280 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  have he : bound (3*4+1) (tightP 4 3) (tightT 4 3) = 6746626690 := by
    norm_num [bound,lam,intercept,tightP,tightT,Nat.factorial]
    rw [hz]
  exact he ▸ tight_word (m:=4) (R:=3) (by decide) (by decide) h w hw

open SuperpermutationLowerBound.ChainReturns in
theorem tight16 (h : Both 5 7) (w : List (Fin 16)) (hw : SuperpermutationBounds.Covers w) :
    22318554323969 ≤ w.length := by
  have hz : ⌈(1852974579452646/21035 : ℚ)⌉₊ = 88090067956 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  have he : bound (3*5+1) (tightP 5 7) (tightT 5 7) = 22318554323969 := by
    norm_num [bound,lam,intercept,tightP,tightT,Nat.factorial]
    rw [hz]
  exact he ▸ tight_word (m:=5) (R:=7) (by decide) (by decide) h w hw

#print axioms tight13
#print axioms tight16
end GeneralAlt
