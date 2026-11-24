import pairs.PeriodicReturns
import pairs.InteriorFullRuns

/- Slot-coordinate argument adapted from Haruhi14/LitBound/Geometry and Pantone et al.'s
   InteriorFullRuns (Apache-2.0). Each final comparison is checked by the kernel. -/
namespace SuperpermutationLowerBound.Refinement.Early16
open PermutationVertex
set_option maxRecDepth 180000
set_option maxHeartbeats 12000000
private def rot (k : ℕ) (i : Fin 16) : Fin 16 :=
  ⟨prefixRotateIndex 16 15 k i, prefixRotateIndex_lt (by decide) i.2⟩

private abbrev norm (w : List Bool) := cellNormalization 15 (by decide) w

private theorem short_row {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 13 w ++ (cellDigits 13 b ++ tail)))
    (hs : s < seg.length) (e : Fin 16 ≃ Alphabet 16)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 15 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 13 w).length ∧
      (seg.actualRun row).length = 13 ∧
      (seg.actualRun row).entry = shortEntry 15 (by decide) ((norm w).symm.trans e) := by
  have ht := h.append_right
  have hg := h.1
  simp only [cellDigits, List.cons_append, List.length_append, List.length_cons] at hg
  have hr : s+(cellWord 13 w).length < seg.length := by omega
  refine ⟨⟨_, hr⟩, rfl, ?_, ?_⟩
  · have hl := ht.actual_length 0 (by simp [cellDigits])
    simpa [cellDigits] using hl
  · exact h.cellWord_entry (n := 15) (by decide) (cells := w) (d := 2)
      (tail := List.replicate (if b then 13-2 else 13-1) 0 ++ tail) (by decide) e he


private noncomputable abbrev entry (off : ℕ) (e : Fin 16 ≃ Alphabet 16) : PermutationVertex 16 :=
  match off with
  | 0 => shortEntry 15 (by decide) e
  | j+1 => fullRunMapPower (by decide) j (fullEntry 15 (by decide) e)
private def index (off slot : ℕ) (i : Fin 16) : Fin 16 :=
  match off with
  | 0 => cellY 15 (by decide) (rot slot i)
  | j+1 => cellU 15 (by decide) ⟨prefixRotateIndex 16 14 j (rot slot i), prefixRotateIndex_lt (by decide) (rot slot i).isLt⟩

private theorem coordinates (off k : ℕ) (e : Fin 16 ≃ Alphabet 16) (i : Fin 16) :
    vertexCoordinates (runMapPower (by decide) k (entry off e)) i = e (index off k i) := by
  rw [runMapPower_coordinates (by decide)]
  cases off with
  | zero => simp only [entry,index,shortEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]
  | succ j =>
    rw [show entry (j+1) e = _ from rfl, fullRunMapPower_coordinates (by decide)]
    simp only [index,fullEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]

private theorem full_row {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 13 w ++ (cellDigits 13 b ++ tail)))
    (hs : s < seg.length) (e : Fin 16 ≃ Alphabet 16)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 15 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 13 w).length+1 ∧
      (seg.actualRun row).length = 15 ∧
      (seg.actualRun row).entry = fullEntry 15 (by decide) ((norm w).symm.trans e) := by
  have ⟨short, hshort, _, hentry⟩ := short_row w b tail h hs e he
  have ht := h.append_right
  have hfin : short = ⟨s+(cellWord 13 w).length, by rw [← hshort]; exact short.isLt⟩ :=
    Fin.ext hshort
  rw [hfin] at hentry
  have hformula := ht.cell_full_entry (n := 15) (by decide) (b := b)
      ((norm w).symm.trans e) hentry
      0 (by cases b <;> decide)
  let g : ℕ := if b then 11 else 12
  have gpos : 0 < g := by cases b <;> decide
  have hs' : 1 < (cellDigits 13 b ++ tail).length := by cases b <;> simp [cellDigits]
  have hl := ht.actual_length 1 hs'
  have hr : s + (cellWord 13 w).length + 1 < seg.length := by have := ht.1; omega
  refine ⟨⟨_,hr⟩,rfl,?_,?_⟩
  · cases b <;> simpa [cellDigits] using hl
  · simpa only [fullRunMapPower, Function.iterate_zero_apply, Nat.add_zero] using hformula

private theorem row_at {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 13 w ++ (cellDigits 13 b ++ tail)))
    (hs : s < seg.length) (e : Fin 16 ≃ Alphabet 16)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 15 (by decide) e)
    (off : ℕ) (hoff : off ≤ if b then 1 else 12) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 13 w).length + off ∧
      (seg.actualRun row).length = (if off = 0 then 13 else 15) ∧
      (seg.actualRun row).entry = entry off ((norm w).symm.trans e) := by
  obtain ⟨short, hshort, lshort, hentry⟩ := short_row w b tail h hs e he
  cases off with
  | zero => exact ⟨short,by omega,lshort,hentry⟩
  | succ j =>
    cases b with
    | false =>
      have hj : j < 12 := by change j+1 ≤ 12 at hoff; omega
      obtain ⟨row,hr,hl,he'⟩ := h.full_after_cells (n := 15) (by decide) hs e he j hj
      refine ⟨row,?_,hl,he'⟩
      change row.val = s+(cellWord 13 w).length+1+j at hr
      omega
    | true =>
      have hzero : j=0 := by change j+1 ≤ 1 at hoff; omega
      subst j
      obtain ⟨row,hr,hl,he'⟩ := full_row w true tail h hs e he
      exact ⟨row,hr,hl,by simpa only [entry,fullRunMapPower,Function.iterate_zero_apply] using he'⟩

theorem exclusion {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (oi oj i j : ℕ) (hi : oi ≤ if b₁ then 1 else 12) (hj : oj ≤ if b₂ then 1 else 12)
    (si : i < if oi=0 then 13 else 15) (sj : j < if oj=0 then 13 else 15)
    (order : (cellWord 13 a).length+oi < (cellWord 13 c).length+oj)
    (hit : ∀ k : Fin 16, (norm a).symm (index oi i k) = (norm c).symm (index oj j k)) :
    ¬ CellFactor 13 ws seg.deficitString := by
  intro hf
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := 15)
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := 15) (by decide)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append,List.length_cons,List.length_nil] at this; omega
  have at₁ : PatternAt seg s (cellWord 13 a ++ (cellDigits 13 b₁ ++ (cellWord 13 ta ++ [2,0]))) := by
    rw [h₁] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  have at₂ : PatternAt seg s (cellWord 13 c ++ (cellDigits 13 b₂ ++ (cellWord 13 tc ++ [2,0]))) := by
    rw [h₂] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := row_at _ _ _ at₁ hs e he oi hi
  obtain ⟨new,id₂,len₂,entry₂⟩ := row_at _ _ _ at₂ hs e he oj hj
  have hne := segment_actualRun_slots_ne seg old new (by omega) i j (by omega) (by omega)
  apply hne
  rw [entry₁,entry₂]
  apply congrArg rotationClass
  apply (show Function.Injective (@vertexCoordinates 16) from fun a b h => by
    simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex h)
  apply Equiv.ext
  intro t
  rw [coordinates,coordinates]
  exact congrArg e (hit t)

theorem miss0 {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor 13 (repeatedCells (completedPair 9 8) 7) seg.deficitString := by
  let ws := repeatedCells (completedPair 9 8) 7
  let a := ws.take 0
  let c := ws.take 109
  have h₁ : ws = a ++ false :: ws.drop (0+1) := by decide
  have h₂ : ws = c ++ false :: ws.drop (109+1) := by decide
  exact exclusion seg ws a c false false _ _ h₁ h₂ 11 2 11 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem miss1 {hk : 7 ≤ 16} {p : OverlapPath 16} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor 13 (repeatedCells (completedPair 8 9) 7) seg.deficitString := by
  let ws := repeatedCells (completedPair 8 9) 7
  let a := ws.take 8
  let c := ws.take 117
  have h₁ : ws = a ++ false :: ws.drop (8+1) := by decide
  have h₂ : ws = c ++ false :: ws.drop (117+1) := by decide
  exact exclusion seg ws a c false false _ _ h₁ h₂ 11 2 11 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms miss0
#print axioms miss1
end SuperpermutationLowerBound.Refinement.Early16
