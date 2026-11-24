module
public import alternation.AlternatingFactors
public import pairs.CompletedFactors

@[expose] public section

namespace GeneralAlt
open SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

private theorem evenPairs (x y r : ℕ) :
    x :: alternatingLengths y x r = (List.replicate (r+1) [x,y]).flatten := by
  induction r with
  | zero => simp [alternatingLengths]
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons]
    simpa [alternatingLengths] using congrArg (fun t => x :: y :: t) ih

private theorem evenPrefix {b R : ℕ} (hR : 0 < R) (hb : 1 ≤ b) (xs : List ℕ)
    (bounded : ∀ x ∈ xs, x ≤ b)
    (h : 2*R ≤ binaryPrefixLength (xs.map (fun x => b-x))) :
    ∃ post, xs = (List.replicate R [b,b-1]).flatten ++ post ∨
            xs = (List.replicate R [b-1,b]).flatten ++ post := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  cases xs with
  | nil => simp [binaryPrefixLength] at h
  | cons x xs =>
    cases xs with
    | nil => simp [binaryPrefixLength] at h; split_ifs at h <;> omega
    | cons y ys =>
      simp only [List.map_cons] at h
      have hh := binaryPrefixLength_two_step (by omega :
        2 ≤ binaryPrefixLength ((b-x)::(b-y)::ys.map (fun z => b-z)))
      have htail : 2*r+1 ≤ binaryPrefixLength ((y::ys).map (fun z => b-z)) := by
        simp only [List.map_cons]; omega
      have hxb := bounded x (by simp)
      have hyb := bounded y (by simp)
      obtain ⟨post, hz | hz⟩ := binaryPrefixLength_chain_factor b r (y::ys)
        (fun z h => bounded z (by simp [h])) htail
      · have hy : y = b := by cases r <;> simp [alternatingLengths] at hz <;> exact hz.1
        have hx : x = b-1 := by omega
        refine ⟨post, Or.inr ?_⟩
        rw [hx, ← evenPairs (b-1) b r]
        exact congrArg (List.cons (b-1)) hz
      · have hy : y = b-1 := by cases r <;> simp [alternatingLengths] at hz <;> exact hz.1
        have hx : x = b := by omega
        refine ⟨post, Or.inl ?_⟩
        rw [hx, ← evenPairs b (b-1) r]
        exact congrArg (List.cons b) hz

/-- The chain after the tested interior supplies the last short separator,
even if that following chain breaks the alternation. -/
theorem interiorCut {a b R : ℕ} {ls d : List ℕ} (hR : 0 < R) (hb : 1 ≤ b)
    (hbound : ∀ x ∈ ls, x ≤ b) (hreal : RealizesChains a ls d)
    (h₁ : ¬ CellFactor a (repeatedCells (completedPair b (b-1)) R) d)
    (h₂ : ¬ CellFactor a (repeatedCells (completedPair (b-1) b) R) d) :
    BoundedAlternation (2*R-1) (interiorLosses b ls) := by
  have aux (mid : List ℕ) (pre post : List ℕ) (hp : post ≠ [])
      (he : ls = pre ++ mid ++ post) :
      BoundedAlternation (2*R-1) (mid.map (fun z => b-z)) := by
    induction mid generalizing pre with
    | nil => trivial
    | cons x xs ih =>
      constructor
      · by_contra! bad
        have hlen : 2*R ≤ binaryPrefixLength ((x::xs).map (fun z => b-z)) := by
          simp only [List.map_cons]; omega
        have forbid (i j : ℕ) (rest : List ℕ)
            (eq : x::xs = (List.replicate R [i,j]).flatten ++ rest) :
            CellFactor a (repeatedCells (completedPair i j) R) d := by
          let ps := (List.replicate R [i,j]).flatten
          have hps : ps ≠ [] := by cases R <;> simp_all [ps,List.replicate_succ]
          have hfac := completedChains_factor pre ps (rest++post) hps (by simp [hp])
          rw [completed_replicate_pairs] at hfac
          apply hreal _
          simpa only [he,eq,List.append_assoc] using hfac
        obtain ⟨rest, eq|eq⟩ := evenPrefix hR hb (x::xs)
          (fun z hz => hbound z (by rw [he]; exact List.mem_append_left _ (List.mem_append_right pre hz))) hlen
        · exact h₁ (forbid _ _ _ eq)
        · exact h₂ (forbid _ _ _ eq)
      · apply ih (pre++[x])
        simpa [List.append_assoc] using he
  cases ls with
  | nil => trivial
  | cons x xs =>
    cases xs with
    | nil => trivial
    | cons y ys =>
      let zs := y::ys
      have hn : zs ≠ [] := by simp [zs]
      have eq := List.dropLast_append_getLast hn
      have ans := aux zs.dropLast [x] [zs.getLast hn] (by simp) (by simpa using congrArg (List.cons x) eq.symm)
      simpa [interiorLosses,zs,List.dropLast_eq_take] using ans

#print axioms interiorCut
end GeneralAlt
