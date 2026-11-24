import SlotGeometry
import AllSizesPublished

/-! A finite scan for repeated occupied coordinates in alternating completed pairs.
The scan compares normalized slots inside two different rows.  For the last
(shortened) cell of a chain it uses its first two rows. -/

namespace GeneralAlt.CollisionFormula
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.SlotDetector
open SuperpermutationLowerBound.Refinement.ChainReturns

/-- The cell number, row offset, and occupied slot of a candidate vertex. -/
abbrev Position (v : ℕ) (ws : List Bool) := Fin ws.length × Fin (v+8) × Fin (v+8)

def admissible (v : ℕ) (ws : List Bool) (x : Position v ws) : Prop :=
  x.2.1.val ≤ (if ws[x.1.val] then 1 else v+4) ∧
  x.2.2.val < (if x.2.1.val=0 then v+5 else v+7)

instance (v : ℕ) (ws : List Bool) (x : Position v ws) : Decidable (admissible v ws x) :=
  by unfold admissible; infer_instance

def row (v : ℕ) (ws : List Bool) (x : Position v ws) : ℕ :=
  (cellWord (v+5) (ws.take x.1.val)).length + x.2.1.val

def atSlot (v : ℕ) (ws : List Bool) (x : Position v ws) (k : Fin (v+8)) : Fin (v+8) :=
  (norm (v:=v) (ws.take x.1.val)).symm (index x.2.1.val x.2.2.val k)

def collision (v : ℕ) (ws : List Bool) : Prop :=
  ∃ x y : Position v ws, admissible v ws x ∧ admissible v ws y ∧
    row v ws x < row v ws y ∧ ∀ k, atSlot v ws x k = atSlot v ws y k

instance (v : ℕ) (ws : List Bool) : Decidable (collision v ws) := by
  unfold collision
  infer_instance

theorem collision_excludes {v : ℕ} {ws : List Bool} (h : collision v ws)
    {hk : 7 ≤ v+8} {p : OverlapPath (v+8)} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) : ¬CellFactor (v+5) ws seg.deficitString := by
  obtain ⟨x,y,hx,hy,hlt,he⟩ := h
  apply exclusion seg ws (ws.take x.1.val) (ws.take y.1.val) ws[x.1.val] ws[y.1.val]
    (ws.drop (x.1.val+1)) (ws.drop (y.1.val+1)) _ _ x.2.1.val y.2.1.val x.2.2.val y.2.2.val
    hx.1 hy.1 hx.2 hy.2 hlt he
  · rw [← List.drop_eq_getElem_cons x.1.isLt, List.take_append_drop]
  · rw [← List.drop_eq_getElem_cons y.1.isLt, List.take_append_drop]

theorem excludes_at {n : ℕ} (hn : 7 ≤ n) {ws : List Bool} (h : collision (n-7) ws)
    {hk : 7 ≤ n+1} {p : OverlapPath (n+1)} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) : ¬CellFactor (n-2) ws seg.deficitString := by
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hn
  have he : n = v+7 := by omega
  clear hv
  subst n
  rw [show v+7-7=v by omega] at h
  rw [show v+7-2 = v+5 by omega]
  exact collision_excludes h seg

def pairHits (m r : ℕ) : Prop :=
  collision (3*m-7) (repeatedCells (completedPair (2*m-1) (2*m-2)) r) ∧
  collision (3*m-7) (repeatedCells (completedPair (2*m-2) (2*m-1)) r)

instance (m r : ℕ) : Decidable (pairHits m r) := by unfold pairHits; infer_instance

theorem both_of_hits (m r : ℕ) (hm : 3 ≤ m) (h : pairHits m r) : Both m r :=
  fun seg => ⟨excludes_at (n:=3*m) (by omega) h.1 seg,
    excludes_at (n:=3*m) (by omega) h.2 seg⟩

/-- Scan increasing positive repeat counts, stopping at the published return. -/
def cutoff (m : ℕ) : ℕ :=
  ((List.range (publicReturn m)).find? (fun k => decide (pairHits m (k+1)))).elim
    (publicReturn m) (·+1)

theorem cutoff_spec (m : ℕ) (hm : 3 ≤ m) :
    1 ≤ cutoff m ∧ cutoff m ≤ publicReturn m ∧ Both m (cutoff m) := by
  unfold cutoff
  cases h : (List.range (publicReturn m)).find? (fun k => decide (pairHits m (k+1))) with
  | none =>
    exact ⟨SuperpermutationBounds.ChainReturns.returnZero_pos (by omega), le_rfl, public_both m hm⟩
  | some k =>
    have hk := List.mem_of_find?_eq_some h
    have hb := List.find?_some h
    exact ⟨by simp, by simpa using (List.mem_range.mp hk),
      both_of_hits m (k+1) hm (of_decide_eq_true hb)⟩

open SuperpermutationLowerBound.ChainReturns in
theorem covering_lower (m : ℕ) (hm : 3 ≤ m) (w : List (Fin (3*m+1)))
    (hw : SuperpermutationBounds.Covers w) :
    bound (3*m+1) (tightP m (cutoff m)) (tightT m (cutoff m)) ≤ w.length :=
  tight_word hm (cutoff_spec m hm).1 (cutoff_spec m hm).2.2 w hw


/-- Every verified pair of witnesses bounds the first-hit cutoff. -/
theorem cutoff_le_of_hits (m k : ℕ) (hm : 3 ≤ m) (h : pairHits m (k+1)) :
    cutoff m ≤ k+1 := by
  by_cases hk : k < publicReturn m
  · unfold cutoff
    cases he : (List.range (publicReturn m)).find? (fun k => decide (pairHits m (k+1))) with
    | none =>
      exact False.elim (List.find?_eq_none.mp he k (List.mem_range.mpr hk) (decide_eq_true h))
    | some u =>
      obtain ⟨_,i,hi,hu,hbefore⟩ := List.find?_eq_some_iff_getElem.mp he
      rw [List.getElem_range] at hu
      by_contra bad
      have hx : k < i := by change ¬ u+1 ≤ k+1 at bad; omega
      have neg := hbefore k hx
      simp [List.getElem_range,h] at neg
  · exact (cutoff_spec m hm).2.1.trans (by omega)

open SuperpermutationLowerBound.ChainReturns

/-- Add the collision estimate to every previous specialization of the
all-sizes bound. The leading maximum also preserves any certified input. -/
noncomputable def allLower (baseline : ℕ → ℕ) (n : ℕ) : ℕ :=
  let m := (n-1)/3
  max (combinedLower baseline n)
    (if n=3*m+1 ∧ 3≤m then bound n (tightP m (cutoff m)) (tightT m (cutoff m)) else 0)

theorem allLower_valid {baseline : ℕ → ℕ} (hb : ValidLower baseline) :
    ValidLower (allLower baseline) := by
  intro n w hw
  apply max_le ((all_sizes hb) n w hw)
  let m := (n-1)/3
  change (if n=3*m+1 ∧ 3≤m then bound n (tightP m (cutoff m)) (tightT m (cutoff m)) else 0) ≤ w.length
  split
  next h =>
    obtain ⟨he,hm⟩ := h
    generalize hj : m = j at he hm ⊢
    subst n
    exact covering_lower j hm w hw
  next => exact Nat.zero_le _

theorem allLower_published : ValidLower (allLower publishedBaseline) :=
  allLower_valid publishedBaseline_valid

#print axioms covering_lower
#print axioms allLower_published
end GeneralAlt.CollisionFormula
