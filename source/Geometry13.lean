import pairs.PeriodicReturns
import pairs.InteriorFullRuns

/- Slot-coordinate argument adapted from Haruhi14/LitBound/Geometry and Pantone et al.'s
   InteriorFullRuns (Apache-2.0). Each final comparison is checked by the kernel. -/
namespace SuperpermutationLowerBound.Refinement.Early13
open PermutationVertex
set_option maxRecDepth 180000
set_option maxHeartbeats 12000000
private def rot (k : ℕ) (i : Fin 13) : Fin 13 :=
  ⟨prefixRotateIndex 13 12 k i, prefixRotateIndex_lt (by decide) i.2⟩

private abbrev norm (w : List Bool) := cellNormalization 12 (by decide) w

private theorem short_row {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 10 w ++ (cellDigits 10 b ++ tail)))
    (hs : s < seg.length) (e : Fin 13 ≃ Alphabet 13)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 12 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 10 w).length ∧
      (seg.actualRun row).length = 10 ∧
      (seg.actualRun row).entry = shortEntry 12 (by decide) ((norm w).symm.trans e) := by
  have ht := h.append_right
  have hg := h.1
  simp only [cellDigits, List.cons_append, List.length_append, List.length_cons] at hg
  have hr : s+(cellWord 10 w).length < seg.length := by omega
  refine ⟨⟨_, hr⟩, rfl, ?_, ?_⟩
  · have hl := ht.actual_length 0 (by simp [cellDigits])
    simpa [cellDigits] using hl
  · exact h.cellWord_entry (n := 12) (by decide) (cells := w) (d := 2)
      (tail := List.replicate (if b then 10-2 else 10-1) 0 ++ tail) (by decide) e he


private noncomputable abbrev entry (off : ℕ) (e : Fin 13 ≃ Alphabet 13) : PermutationVertex 13 :=
  match off with
  | 0 => shortEntry 12 (by decide) e
  | j+1 => fullRunMapPower (by decide) j (fullEntry 12 (by decide) e)
private def index (off slot : ℕ) (i : Fin 13) : Fin 13 :=
  match off with
  | 0 => cellY 12 (by decide) (rot slot i)
  | j+1 => cellU 12 (by decide) ⟨prefixRotateIndex 13 11 j (rot slot i), prefixRotateIndex_lt (by decide) (rot slot i).isLt⟩

private theorem coordinates (off k : ℕ) (e : Fin 13 ≃ Alphabet 13) (i : Fin 13) :
    vertexCoordinates (runMapPower (by decide) k (entry off e)) i = e (index off k i) := by
  rw [runMapPower_coordinates (by decide)]
  cases off with
  | zero => simp only [entry,index,shortEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]
  | succ j =>
    rw [show entry (j+1) e = _ from rfl, fullRunMapPower_coordinates (by decide)]
    simp only [index,fullEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]

private theorem full_row {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 10 w ++ (cellDigits 10 b ++ tail)))
    (hs : s < seg.length) (e : Fin 13 ≃ Alphabet 13)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 12 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 10 w).length+1 ∧
      (seg.actualRun row).length = 12 ∧
      (seg.actualRun row).entry = fullEntry 12 (by decide) ((norm w).symm.trans e) := by
  have ⟨short, hshort, _, hentry⟩ := short_row w b tail h hs e he
  have ht := h.append_right
  have hfin : short = ⟨s+(cellWord 10 w).length, by rw [← hshort]; exact short.isLt⟩ :=
    Fin.ext hshort
  rw [hfin] at hentry
  have hformula := ht.cell_full_entry (n := 12) (by decide) (b := b)
      ((norm w).symm.trans e) hentry
      0 (by cases b <;> decide)
  let g : ℕ := if b then 8 else 9
  have gpos : 0 < g := by cases b <;> decide
  have hs' : 1 < (cellDigits 10 b ++ tail).length := by cases b <;> simp [cellDigits]
  have hl := ht.actual_length 1 hs'
  have hr : s + (cellWord 10 w).length + 1 < seg.length := by have := ht.1; omega
  refine ⟨⟨_,hr⟩,rfl,?_,?_⟩
  · cases b <;> simpa [cellDigits] using hl
  · simpa only [fullRunMapPower, Function.iterate_zero_apply, Nat.add_zero] using hformula

private theorem row_at {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 10 w ++ (cellDigits 10 b ++ tail)))
    (hs : s < seg.length) (e : Fin 13 ≃ Alphabet 13)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 12 (by decide) e)
    (off : ℕ) (hoff : off ≤ if b then 1 else 9) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 10 w).length + off ∧
      (seg.actualRun row).length = (if off = 0 then 10 else 12) ∧
      (seg.actualRun row).entry = entry off ((norm w).symm.trans e) := by
  obtain ⟨short, hshort, lshort, hentry⟩ := short_row w b tail h hs e he
  cases off with
  | zero => exact ⟨short,by omega,lshort,hentry⟩
  | succ j =>
    cases b with
    | false =>
      have hj : j < 9 := by change j+1 ≤ 9 at hoff; omega
      obtain ⟨row,hr,hl,he'⟩ := h.full_after_cells (n := 12) (by decide) hs e he j hj
      refine ⟨row,?_,hl,he'⟩
      change row.val = s+(cellWord 10 w).length+1+j at hr
      omega
    | true =>
      have hzero : j=0 := by change j+1 ≤ 1 at hoff; omega
      subst j
      obtain ⟨row,hr,hl,he'⟩ := full_row w true tail h hs e he
      exact ⟨row,hr,hl,by simpa only [entry,fullRunMapPower,Function.iterate_zero_apply] using he'⟩

theorem exclusion {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (oi oj i j : ℕ) (hi : oi ≤ if b₁ then 1 else 9) (hj : oj ≤ if b₂ then 1 else 9)
    (si : i < if oi=0 then 10 else 12) (sj : j < if oj=0 then 10 else 12)
    (order : (cellWord 10 a).length+oi < (cellWord 10 c).length+oj)
    (hit : ∀ k : Fin 13, (norm a).symm (index oi i k) = (norm c).symm (index oj j k)) :
    ¬ CellFactor 10 ws seg.deficitString := by
  intro hf
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := 12)
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := 12) (by decide)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append,List.length_cons,List.length_nil] at this; omega
  have at₁ : PatternAt seg s (cellWord 10 a ++ (cellDigits 10 b₁ ++ (cellWord 10 ta ++ [2,0]))) := by
    rw [h₁] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  have at₂ : PatternAt seg s (cellWord 10 c ++ (cellDigits 10 b₂ ++ (cellWord 10 tc ++ [2,0]))) := by
    rw [h₂] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := row_at _ _ _ at₁ hs e he oi hi
  obtain ⟨new,id₂,len₂,entry₂⟩ := row_at _ _ _ at₂ hs e he oj hj
  have hne := segment_actualRun_slots_ne seg old new (by omega) i j (by omega) (by omega)
  apply hne
  rw [entry₁,entry₂]
  apply congrArg rotationClass
  apply (show Function.Injective (@vertexCoordinates 13) from fun a b h => by
    simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex h)
  apply Equiv.ext
  intro t
  rw [coordinates,coordinates]
  exact congrArg e (hit t)

theorem miss0 {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor 10 (repeatedCells (completedPair 7 6) 3) seg.deficitString := by
  let ws := repeatedCells (completedPair 7 6) 3
  let a := ws.take 0
  let c := ws.take 32
  have h₁ : ws = a ++ false :: ws.drop (0+1) := by decide
  have h₂ : ws = c ++ true :: ws.drop (32+1) := by decide
  exact exclusion seg ws a c false true _ _ h₁ h₂ 0 0 8 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem miss1 {hk : 7 ≤ 13} {p : OverlapPath 13} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor 10 (repeatedCells (completedPair 6 7) 3) seg.deficitString := by
  let ws := repeatedCells (completedPair 6 7) 3
  let a := ws.take 6
  let c := ws.take 38
  have h₁ : ws = a ++ false :: ws.drop (6+1) := by decide
  have h₂ : ws = c ++ true :: ws.drop (38+1) := by decide
  exact exclusion seg ws a c false true _ _ h₁ h₂ 0 0 8 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms miss0
#print axioms miss1
end SuperpermutationLowerBound.Refinement.Early13
