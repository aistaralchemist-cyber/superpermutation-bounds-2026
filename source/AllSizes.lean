import PublishedCompare
import FiniteCertificates

/-! The piecewise improvement can be combined with any word-level bound,
including a stronger bound known at one particular alphabet size. -/
namespace GeneralAlt
open SuperpermutationLowerBound.ChainReturns

def ValidLower (B : ℕ → ℕ) : Prop :=
  ∀ n (w : List (Fin n)), SuperpermutationBounds.Covers w → B n ≤ w.length

noncomputable def residueLower (n : ℕ) : ℕ :=
  let m := (n-1)/3
  if n=3*m+1 ∧ 3≤m then bound n (tightP m (publicReturn m)) (tightT m (publicReturn m))
  else 0

theorem valid_residue : ValidLower residueLower := by
  intro n w hw
  unfold residueLower
  let m := (n-1)/3
  change (if n=3*m+1 ∧ 3≤m then _ else _) ≤ _
  split
  next h =>
    rcases h with ⟨e,hm⟩
    generalize hj : m = j at e hm ⊢
    subst n
    simpa using word_general j hm w hw
  next => exact Nat.zero_le _

def finiteLower (n : ℕ) : ℕ :=
  if n=13 then 6746626690 else if n=16 then 22318554323969 else 0

theorem valid_finite : ValidLower finiteLower := by
  intro n w hw
  unfold finiteLower
  split
  next h => subst n; exact EarlyAlternation.lower_thirteen w hw
  next =>
    split
    next h => subst n; exact EarlyAlternation.lower_sixteen w hw
    next => exact Nat.zero_le _

noncomputable def combinedLower (baseline : ℕ → ℕ) (n : ℕ) : ℕ :=
  max (baseline n) (max (residueLower n) (finiteLower n))

theorem all_sizes {baseline : ℕ → ℕ} (known : ValidLower baseline) :
    ValidLower (combinedLower baseline) := by
  intro n w hw
  exact max_le (known n w hw) (max_le (valid_residue n w hw) (valid_finite n w hw))

theorem alphabet_lower : ValidLower id := by
  intro n w hw
  obtain ⟨u,v,e⟩ := hw (List.finRange n) (by simp) (List.nodup_finRange n)
  simp [e]; omega

/-- No input bound is required for the elementary version. -/
theorem all_sizes_unconditional : ValidLower (combinedLower id) := all_sizes alphabet_lower

#print axioms all_sizes
#print axioms all_sizes_unconditional
end GeneralAlt
