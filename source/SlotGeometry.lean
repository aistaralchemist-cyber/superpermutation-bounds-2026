import pairs.PeriodicReturns
import pairs.InteriorFullRuns

/- Slot-coordinate argument adapted from Haruhi14/LitBound/Geometry and Pantone et al.'s
   InteriorFullRuns (Apache-2.0). The bounds below are uniform in every alphabet size v+8. -/
namespace SuperpermutationLowerBound.Refinement.SlotDetector
open PermutationVertex
variable {v : ℕ}
set_option maxRecDepth 180000
set_option maxHeartbeats 12000000
private def rot (k : ℕ) (i : Fin (v+8)) : Fin (v+8) :=
  ⟨prefixRotateIndex (v+8) (v+7) k i, prefixRotateIndex_lt (by omega) i.2⟩

abbrev norm (w : List Bool) := cellNormalization (v+7) (by omega) w

private theorem short_row {hk : 7 ≤ (v+8)} {p : OverlapPath (v+8)} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord (v+5) w ++ (cellDigits (v+5) b ++ tail)))
    (hs : s < seg.length) (e : Fin (v+8) ≃ Alphabet (v+8))
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry (v+7) (by omega) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord (v+5) w).length ∧
      (seg.actualRun row).length = (v+5) ∧
      (seg.actualRun row).entry = shortEntry (v+7) (by omega) ((norm (v:=v) w).symm.trans e) := by
  have ht := h.append_right
  have hg := h.1
  simp only [cellDigits, List.cons_append, List.length_append, List.length_cons] at hg
  have hr : s+(cellWord (v+5) w).length < seg.length := by omega
  refine ⟨⟨_, hr⟩, rfl, ?_, ?_⟩
  · have hl := ht.actual_length 0 (by simp [cellDigits])
    simpa [cellDigits] using hl
  · apply h.cellWord_entry (n := (v+7)) (by omega) (cells := w) (d := 2)
      (tail := List.replicate (if b then (v+5)-2 else (v+5)-1) 0 ++ tail) (by omega) e he


private noncomputable abbrev entry (off : ℕ) (e : Fin (v+8) ≃ Alphabet (v+8)) : PermutationVertex (v+8) :=
  match off with
  | 0 => shortEntry (v+7) (by omega) e
  | j+1 => fullRunMapPower (by omega) j (fullEntry (v+7) (by omega) e)
def index (off slot : ℕ) (i : Fin (v+8)) : Fin (v+8) :=
  match off with
  | 0 => cellY (v+7) (by omega) (rot slot i)
  | j+1 => cellU (v+7) (by omega) ⟨prefixRotateIndex (v+8) (v+6) j (rot slot i), prefixRotateIndex_lt (by omega) (rot slot i).isLt⟩

private theorem coordinates (off k : ℕ) (e : Fin (v+8) ≃ Alphabet (v+8)) (i : Fin (v+8)) :
    vertexCoordinates (runMapPower (by omega) k (entry off e)) i = e (index off k i) := by
  rw [runMapPower_coordinates (by omega)]
  cases off with
  | zero => simp only [entry,index,shortEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot, show v+8-1=v+7 by omega]
  | succ j =>
    rw [show entry (j+1) e = _ from rfl, fullRunMapPower_coordinates (by omega)]
    simp only [index,fullEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot, show v+8-1=v+7 by omega, show v+8-2=v+6 by omega]

private theorem full_row {hk : 7 ≤ (v+8)} {p : OverlapPath (v+8)} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord (v+5) w ++ (cellDigits (v+5) b ++ tail)))
    (hs : s < seg.length) (e : Fin (v+8) ≃ Alphabet (v+8))
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry (v+7) (by omega) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord (v+5) w).length+1 ∧
      (seg.actualRun row).length = (v+7) ∧
      (seg.actualRun row).entry = fullEntry (v+7) (by omega) ((norm (v:=v) w).symm.trans e) := by
  have ⟨short, hshort, _, hentry⟩ := short_row w b tail h hs e he
  have ht := h.append_right
  have hfin : short = ⟨s+(cellWord (v+5) w).length, by rw [← hshort]; exact short.isLt⟩ :=
    Fin.ext hshort
  rw [hfin] at hentry
  have hformula := ht.cell_full_entry (n := (v+7)) (by omega) (b := b)
      ((norm (v:=v) w).symm.trans e) hentry
      0 (by cases b <;> simp)
  
  have hs' : 1 < (cellDigits (v+5) b ++ tail).length := by cases b <;> simp [cellDigits]
  have hl := ht.actual_length 1 hs'
  have hr : s + (cellWord (v+5) w).length + 1 < seg.length := by have := ht.1; omega
  refine ⟨⟨_,hr⟩,rfl,?_,?_⟩
  · cases b <;> simpa [cellDigits] using hl
  · simpa only [fullRunMapPower, Function.iterate_zero_apply, Nat.add_zero] using hformula

private theorem row_at {hk : 7 ≤ (v+8)} {p : OverlapPath (v+8)} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord (v+5) w ++ (cellDigits (v+5) b ++ tail)))
    (hs : s < seg.length) (e : Fin (v+8) ≃ Alphabet (v+8))
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry (v+7) (by omega) e)
    (off : ℕ) (hoff : off ≤ if b then 1 else (v+4)) :
    ∃ row : Fin seg.length, row.val = s + (cellWord (v+5) w).length + off ∧
      (seg.actualRun row).length = (if off = 0 then (v+5) else (v+7)) ∧
      (seg.actualRun row).entry = entry off ((norm (v:=v) w).symm.trans e) := by
  obtain ⟨short, hshort, lshort, hentry⟩ := short_row w b tail h hs e he
  cases off with
  | zero => exact ⟨short,by omega,lshort,hentry⟩
  | succ j =>
    cases b with
    | false =>
      have hj : j < (v+4) := by change j+1 ≤ (v+4) at hoff; omega
      obtain ⟨row,hr,hl,he'⟩ := h.full_after_cells (n := (v+7)) (by omega) hs e he j hj
      refine ⟨row,?_,hl,he'⟩
      change row.val = s+(cellWord (v+5) w).length+1+j at hr
      omega
    | true =>
      have hzero : j=0 := by change j+1 ≤ 1 at hoff; omega
      subst j
      obtain ⟨row,hr,hl,he'⟩ := full_row w true tail h hs e he
      exact ⟨row,hr,hl,by simpa only [entry,fullRunMapPower,Function.iterate_zero_apply] using he'⟩

theorem exclusion {hk : 7 ≤ (v+8)} {p : OverlapPath (v+8)} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (oi oj i j : ℕ) (hi : oi ≤ if b₁ then 1 else (v+4)) (hj : oj ≤ if b₂ then 1 else (v+4))
    (si : i < if oi=0 then (v+5) else (v+7)) (sj : j < if oj=0 then (v+5) else (v+7))
    (order : (cellWord (v+5) a).length+oi < (cellWord (v+5) c).length+oj)
    (hit : ∀ k : Fin (v+8), (norm (v:=v) a).symm (index oi i k) = (norm (v:=v) c).symm (index oj j k)) :
    ¬ CellFactor (v+5) ws seg.deficitString := by
  intro hf
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := (v+7))
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := (v+7)) (by omega)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append,List.length_cons,List.length_nil] at this; omega
  have at₁ : PatternAt seg s (cellWord (v+5) a ++ (cellDigits (v+5) b₁ ++ (cellWord (v+5) ta ++ [2,0]))) := by
    rw [h₁] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc, show v+7-2=v+5 by omega] using h
  have at₂ : PatternAt seg s (cellWord (v+5) c ++ (cellDigits (v+5) b₂ ++ (cellWord (v+5) tc ++ [2,0]))) := by
    rw [h₂] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc, show v+7-2=v+5 by omega] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := row_at _ _ _ at₁ hs e he oi hi
  obtain ⟨new,id₂,len₂,entry₂⟩ := row_at _ _ _ at₂ hs e he oj hj
  have hne := segment_actualRun_slots_ne seg old new (by omega) i j (by omega) (by omega)
  apply hne
  rw [entry₁,entry₂]
  apply congrArg rotationClass
  apply (show Function.Injective (@vertexCoordinates (v+8)) from fun a b h => by
    simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex h)
  apply Equiv.ext
  intro t
  rw [coordinates,coordinates]
  exact congrArg e (hit t)

end SuperpermutationLowerBound.Refinement.SlotDetector
