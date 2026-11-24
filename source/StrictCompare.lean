module

public import TightGeneral
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound.ChainReturns
private def cq (n : ℚ) := n*(n-2)-2
private def den (n t : ℚ) := cq n*t-2*n
private def numer (n m F t : ℚ) := ((n-2)*t-2)*(F-2)-16*m

private theorem growth (n : ℕ) (hn : 15 ≤ n) : 2*n^10 ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h := Nat.pow_le_pow_left (show 4*(n+1) ≤ 5*n by omega) 10
    rw [mul_pow,mul_pow] at h
    norm_num at h
    have h16 : (n+1)^10 ≤ 16*n^10 := by omega
    have hm := Nat.mul_le_mul_left (2*n^10) (show 16 ≤ n+1 by omega)
    rw [Nat.factorial_succ]
    calc
      _ ≤ (n+1)*(2*n^10) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ ih

/-- Compare the rational transfer fractions at both slopes. -/
private theorem rational_step {n m F R : ℚ} (hn : 15 ≤ n) (hm : n=3*m)
    (hR : 1 ≤ R) (hrange : 4*R ≤ n^2) (hF : 2*n^10 ≤ F) :
    let t₀:=4*m-3-1/(2*R)
    let t₁:=4*m-3-1/(2*R-1)
    0 ≤ numer n m F t₀ / den n t₀ ∧
    numer n m F t₀ / den n t₀ + 4 ≤ numer n m F t₁ / den n t₁ := by
  let t₀:=4*m-3-1/(2*R)
  let t₁:=4*m-3-1/(2*R-1)
  change 0 ≤ numer n m F t₀ / den n t₀ ∧
    numer n m F t₀ / den n t₀ + 4 ≤ numer n m F t₁ / den n t₁
  have r₀ : 0 < 2*R := by linarith
  have r₁ : 0 < 2*R-1 := by linarith
  have u₀ : 1/(2*R) ≤ 1 := (div_le_one r₀).2 (by linarith)
  have u₁ : 1/(2*R-1) ≤ 1 := (div_le_one r₁).2 (by linarith)
  have ts₀ : 1 ≤ t₀ ∧ t₀ ≤ 2*n := by
    dsimp [t₀]; constructor <;> linarith [div_pos (by norm_num : (0:ℚ)<1) r₀]
  have ts₁ : 1 ≤ t₁ ∧ t₁ ≤ 2*n := by
    dsimp [t₁]; constructor <;> linarith [div_pos (by norm_num : (0:ℚ)<1) r₁]
  have cn : 2*n+1 ≤ cq n := by
    unfold cq; nlinarith [mul_nonneg (show 0≤n by linarith) (show 0≤n-15 by linarith)]
  have cb : cq n ≤ n^2 := by unfold cq; nlinarith
  have de {t : ℚ} (ht : 1 ≤ t ∧ t ≤ 2*n) :
      0 < den n t ∧ den n t ≤ 2*n^3 := by
    unfold den
    have ct := mul_le_mul_of_nonneg_left ht.1 (show 0 ≤ cq n by linarith)
    have ce := mul_le_mul cb ht.2 (by linarith : 0 ≤ t) (sq_nonneg n)
    constructor <;> nlinarith
  have de₀ := de ts₀
  have de₁ := de ts₁
  have nn : 1 ≤ n := by linarith
  have fourth : n^4 ≤ n^10 := pow_le_pow_right₀ nn (by decide)
  have cube : 1 ≤ n^3 := one_le_pow₀ nn
  have ccc := mul_le_mul_of_nonneg_left cb (show 0 ≤ 8*m by linarith)
  have fbig : 8*m*cq n+4 ≤ F := by
    have prod := mul_nonneg (show 0 ≤ n-15 by linarith) (show 0 ≤ n^3 by linarith)
    rw [show 8*m = (8/3:ℚ)*n by linarith] at ccc
    nlinarith
  have strong : 2*F ≤ 4*(F-2)-16*m*cq n := by linarith
  have rn := mul_self_le_mul_self (by linarith : (0:ℚ)≤4*R) hrange
  have rden : (2*R)*(2*R-1) ≤ n^4/4 := by nlinarith
  have dd := mul_le_mul de₀.2 de₁.2 (le_of_lt de₁.1)
    (show 0 ≤ 2*n^3 by linarith)
  have dd' : den n t₀ * den n t₁ ≤ 4*n^6 := by nlinarith
  have all := mul_le_mul rden dd' (mul_nonneg (le_of_lt de₀.1) (le_of_lt de₁.1))
    (show 0 ≤ n^4/4 by positivity)
  let B := (2*R)*(2*R-1)*(den n t₀ * den n t₁)
  have hB : B ≤ n^10 := by dsimp [B]; nlinarith
  have hBpos : 0 < B := mul_pos (mul_pos r₀ r₁) (mul_pos de₀.1 de₁.1)
  have better : (4:ℚ) ≤ (4*(F-2)-16*m*cq n)/B := (le_div_iff₀ hBpos).2 (by linarith)
  have diff : numer n m F t₁ / den n t₁ - numer n m F t₀ / den n t₀ =
      (4*(F-2)-16*m*cq n)/B := by
    dsimp only [B]
    field_simp [ne_of_gt r₀,ne_of_gt r₁,ne_of_gt de₀.1,ne_of_gt de₁.1]
    unfold numer den cq
    dsimp only [t₀,t₁]
    field_simp
    ring
  have pos : 0 ≤ numer n m F t₀ := by
    have c2 : (2:ℚ) ≤ cq n := by linarith
    have k:= mul_le_mul_of_nonneg_left c2 (show 0 ≤ 8*m by linarith)
    have f16 : 16*m ≤ F-2 := by linarith
    have he := mul_le_mul_of_nonneg_left ts₀.1 (show 0 ≤ n-2 by linarith)
    have e2 : 1 ≤ (n-2)*t₀-2 := by linarith
    have k2:= mul_le_mul_of_nonneg_right e2 (show 0 ≤ F-2 by linarith)
    unfold numer
    linarith
  exact ⟨div_nonneg pos (le_of_lt de₀.1),by linarith⟩

private theorem rational_form (n : ℕ) (m p t : ℚ) (h : 2*p+t=8*m-2) :
    (lam n t*(n.factorial:ℚ)-intercept n p t)/((n:ℚ)*lam n t-2*t) =
      numer n m n.factorial t / den n t := by
  have hN : lam n t*(n.factorial:ℚ)-intercept n p t=numer n m n.factorial t := by
    unfold lam intercept numer
    linarith only [h]
  have hD : (n:ℚ)*lam n t-2*t=den n t := by unfold lam den cq; ring
  rw [hN,hD]

/-- For every common return length R with 4R≤(3m)^2 the tighter interior
increases the *integer* word bound by at least four at K=3m+1≥16. -/
theorem strict_four {m R : ℕ} (hm : 5≤m) (hR : 1≤R) (hmax : 4*R≤(3*m)^2) :
    bound (3*m+1) (priceP m R) (priceT m R)+4 ≤
      bound (3*m+1) (tightP m R) (tightT m R) := by
  let n:=3*m
  have hn : 15≤n := by dsimp [n]; omega
  have hqr : (1:ℚ) ≤ R := by exact_mod_cast hR
  have hcut : ((2*R-1:ℕ):ℚ) = 2*(R:ℚ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*R)]; push_cast; rfl
  have hp0 : 2*priceP m R+priceT m R=8*(m:ℚ)-2 := by
    unfold priceP priceT; ring
  have hp1 : 2*tightP m R+tightT m R=8*(m:ℚ)-2 := by
    unfold tightP tightT; ring
  have h := rational_step (n:=(n:ℚ)) (m:=(m:ℚ)) (F:=(n.factorial:ℚ)) (R:=(R:ℚ))
    (by exact_mod_cast hn) (by dsimp [n]; push_cast; rfl) hqr
    (by exact_mod_cast hmax) (by exact_mod_cast growth n hn)
  change 0 ≤ numer n m n.factorial (priceT m R) / den n (priceT m R) ∧
    numer n m n.factorial (priceT m R) / den n (priceT m R) + 4 ≤
    numer n m n.factorial (4*(m:ℚ)-3-1/(2*(R:ℚ)-1)) / den n (4*(m:ℚ)-3-1/(2*(R:ℚ)-1)) at h
  have te : tightT m R=4*(m:ℚ)-3-1/(2*(R:ℚ)-1) := by unfold tightT; rw [hcut]
  rw [←te] at h
  have hc := Nat.ceil_mono h.2
  rw [Nat.ceil_add_ofNat h.1 4] at hc
  unfold bound
  simp only [Nat.add_sub_cancel]
  rw [rational_form (3*m) m _ _ hp0, rational_form (3*m) m _ _ hp1, Nat.add_assoc]
  exact Nat.add_le_add_left hc _

theorem public_strict (m : ℕ) (hm : 5≤m) :
    bound (3*m+1) (priceP m (publicReturn m)) (priceT m (publicReturn m))+4 ≤
    bound (3*m+1) (tightP m (publicReturn m)) (tightT m (publicReturn m)) :=
  strict_four hm (SuperpermutationBounds.ChainReturns.returnZero_pos (by omega))
    (SuperpermutationBounds.ChainReturns.returnZero_quadratic (by omega))

#print axioms public_strict
end GeneralAlt
