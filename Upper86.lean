import Asym22.LogRate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Superperm86

/-- On the domain log u ≥ 2, passing from u to a larger v increases u/(log u)^2. -/
theorem scaled_log_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hlog : 2 ≤ Real.log u) :
    u * (Real.log v)^2 ≤ v * (Real.log u)^2 := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  let x := Real.sqrt (v/u)
  have hx1 : 1 ≤ x := by
    have h := Real.sqrt_le_sqrt ((one_le_div hu).mpr huv)
    simpa [x] using h
  have hx : 0 < x := by linarith only [hx1]
  have hx2 : x^2 * u = v := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hxlog : Real.log x = (Real.log v - Real.log u)/2 := by
    dsimp [x]; rw [Real.log_sqrt (by positivity), Real.log_div hv.ne' hu.ne']
  have hvlog : Real.log v ≤ x * Real.log u := by
    have he := Real.log_le_sub_one_of_pos hx
    nlinarith only [he, hxlog, mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hlog)]
  have hlv := (show 0 ≤ Real.log v by linarith only [Real.log_le_log hu huv, hlog])
  have hs := pow_le_pow_left₀ hlv hvlog 2
  calc
    u * (Real.log v)^2 ≤ u * (x * Real.log u)^2 := mul_le_mul_of_nonneg_left hs hu.le
    _ = v * (Real.log u)^2 := by rw [←hx2]; ring

/-- Scalar reduction of a parameter certificate to the logarithmic error rate. -/
theorem parameter_bound {n T r : ℝ} (hn : 0 < n) (hT : n ≤ T) (hlog : 2 ≤ Real.log n)
    (hr : 0 < r) (hc : (26:ℝ)^20 * T ≤ (86*r)^20 * (Real.log T)^2) :
    26/r ≤ 86 * (Real.log n)^(1/10:ℝ) * n^(-1/20:ℝ) := by
  have hTp := lt_of_lt_of_le hn hT
  have hL : 0 ≤ Real.log n := by linarith
  have hd : n*26^20 ≤ (86*r)^20*(Real.log n)^2 := by
    apply le_of_mul_le_mul_right (a := T) _ hTp
    calc
      n*26^20*T = n*(26^20*T) := by ring
      _ ≤ n*((86*r)^20*(Real.log T)^2) := mul_le_mul_of_nonneg_left hc hn.le
      _ = (86*r)^20*(n*(Real.log T)^2) := by ring
      _ ≤ (86*r)^20*(T*(Real.log n)^2) :=
        mul_le_mul_of_nonneg_left (scaled_log_mono hn hT hlog) (by positivity)
      _ = (86*r)^20*(Real.log n)^2*T := by ring
  have hz := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ n*26^20) hd (by norm_num : (0:ℝ) ≤ 1/20)
  have h26 : ((26:ℝ)^20)^(1/20:ℝ) = 26 :=
    by simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 26) (by decide : (20:ℕ) ≠ 0)
  have h86 : ((86*r)^20)^(1/20:ℝ) = 86*r :=
    by simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (show 0 ≤ 86*r by positivity) (by decide : (20:ℕ) ≠ 0)
  have hpow : ((Real.log n)^2)^(1/20:ℝ) = (Real.log n)^(1/10:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  rw [Real.mul_rpow hn.le (by positivity),Real.mul_rpow (by positivity) (sq_nonneg _),h26,h86,hpow] at hz
  rw [show (-1/20:ℝ) = -(1/20:ℝ) by ring, Real.rpow_neg hn.le, ←div_eq_mul_inv,
    div_le_div_iff₀ hr (Real.rpow_pos_of_pos hn _)]
  linarith only [hz]

end Superperm86

namespace Superperm86
def C : ℕ := 2904 * 10400^2
def lam (s : ℕ) : ℕ := Nat.log 2 s + 2
def thresh (s : ℕ) : ℕ := C*s^20*(lam s)^2

private theorem log_lower {x : ℕ} (hx : 2^98 ≤ x) : (67:ℝ) ≤ Real.log x := by
  have hh : (2:ℝ)^98 ≤ x := by exact_mod_cast hx
  have he := Real.log_le_log (by norm_num : (0:ℝ)<2^98) hh
  rw [Real.log_pow] at he
  push_cast at he
  linarith only [he,Real.log_two_gt_d9]

private theorem certificate6 :
    (26:ℝ)^20 * (thresh 7 : ℝ) ≤ (86*(6:ℝ))^20 * (Real.log (thresh 7 : ℝ))^2 := by
  have h := log_lower (x:=thresh 7) (by decide)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 67) h 2
  have hh : thresh 7 = 314096640000*7^20*16 := by decide
  calc
    _ ≤ (86*(6:ℝ))^20 * 67^2 := by rw [hh]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

private theorem log_threshold (s : ℕ) (hs : 7 ≤ s) :
    (69/5:ℝ)*(lam s : ℝ) ≤ Real.log (thresh s : ℝ) := by
  have hf : 4 ≤ lam s := by
    have H := Nat.log_mono_right (b:=2) hs
    change 4 ≤ Nat.log 2 s + 2
    have : Nat.log 2 7 = 2 := by decide
    omega
  have hbase : 2^40 ≤ C*(lam s)^2 := by
    calc
      _ ≤ C*4^2 := by decide
      _ ≤ _ := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hf 2)
  have hsmall := Nat.pow_log_le_self 2 (show s≠0 by omega)
  have hlarge : 2^(20*lam s) ≤ thresh s := by
    calc
      _ = (2^(Nat.log 2 s))^20 * 2^40 := by
        rw [←pow_mul, ←pow_add, lam]; congr 1; omega
      _ ≤ s^20 * (C*(lam s)^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hsmall 20) hbase
      _ = _ := by unfold thresh; ring
  have hlargeR : (2:ℝ)^(20*lam s) ≤ (thresh s :ℝ) := by exact_mod_cast hlarge
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^(20*lam s)) hlargeR
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hlow : (69/100:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlow (show (0:ℝ) ≤ 20*(lam s:ℝ) by positivity)
  linarith only [hlog,hmul]

theorem certificate (r : ℕ) (hr : 6 ≤ r) :
    (26:ℝ)^20 * (thresh (r+1) : ℝ) ≤ (86*(r:ℝ))^20 * (Real.log (thresh (r+1) : ℝ))^2 := by
  rcases hr.eq_or_lt with h | h
  · subst r; exact certificate6
  have hr7 : (7:ℝ) ≤ r := by exact_mod_cast (show 7 ≤ r by omega)
  have hsr : ((r+1 : ℕ):ℝ) ≤ 8/7*(r:ℝ) := by push_cast; linarith
  have hs20 := pow_le_pow_left₀ (by positivity : 0 ≤ ((r+1 : ℕ):ℝ)) hsr 20
  have sq := pow_le_pow_left₀ (show (0:ℝ) ≤ 69/5*(lam (r+1):ℝ) by positivity)
    (log_threshold (r+1) (by omega)) 2
  have hcoef : (26:ℝ)^20*(C:ℝ)*(8/7)^20 ≤ 86^20*(69/5)^2 := by norm_num [C]
  calc
    _ = 26^20*(C:ℝ)*((r+1:ℕ):ℝ)^20*(lam (r+1):ℝ)^2 := by unfold thresh; push_cast; ring
    _ ≤ 26^20*(C:ℝ)*(8/7*(r:ℝ))^20*(lam (r+1):ℝ)^2 := by gcongr
    _ = (26^20*(C:ℝ)*(8/7)^20)*((r:ℝ)^20*(lam (r+1):ℝ)^2) := by ring
    _ ≤ (86^20*(69/5)^2)*((r:ℝ)^20*(lam (r+1):ℝ)^2) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (86*(r:ℝ))^20*((69/5)*(lam (r+1):ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left sq (by positivity)

theorem logn_two (n : ℕ) (hn : thresh 6 ≤ n) : (2:ℝ) ≤ Real.log n := by
  have hp : (2:ℝ)^4 ≤ n := by exact_mod_cast (le_trans (by decide : 2^4 ≤ thresh 6) hn)
  have hh := Real.log_le_log (by norm_num : (0:ℝ) < 2^4) hp
  rw [Real.log_pow] at hh
  push_cast at hh
  linarith only [hh, Real.log_two_gt_d9]


/-- The greatest admissible integer parameter certifies the uniform logarithmic rate. -/
theorem all_parameters (n : ℕ) (hn : thresh 6 ≤ n) :
    ∃ r : ℕ, 6 ≤ r ∧ thresh r ≤ n ∧
      26/(r:ℝ) ≤ 86*(Real.log n)^(1/10:ℝ)*(n:ℝ)^(-1/20:ℝ) := by
  let P : ℕ → Prop := fun j => thresh j ≤ n
  have fits (j : ℕ) (h : P j) : j ≤ n := by
    have c : 1 ≤ C := by decide
    have l : 1 ≤ lam j ^ 2 := Nat.one_le_pow _ _ (by dsimp [lam]; omega)
    calc
      j ≤ j^20 := Nat.le_pow (by decide : 0<20)
      _ ≤ C*j^20 := by simpa using Nat.mul_le_mul_right (j^20) c
      _ ≤ thresh j := by simpa [thresh] using Nat.mul_le_mul_left (C*j^20) l
      _ ≤ n := h
  let r := Nat.findGreatest P n
  have hr : 6 ≤ r := Nat.le_findGreatest (fits 6 hn) hn
  have hfit : P r := Nat.findGreatest_spec (fits 6 hn) hn
  have hnxt : n < thresh (r+1) := by
    by_contra! h
    exact Nat.findGreatest_is_greatest (P:=P) (n:=n) (show r < r+1 by omega) (fits _ h) h
  have hn0 : 0 < n := (by decide : 0 < thresh 6).trans_le hn
  exact ⟨r, hr, hfit, parameter_bound (n := (n:ℝ)) (T := (thresh (r+1):ℝ)) (r:=(r:ℝ))
    (by exact_mod_cast hn0) (by exact_mod_cast hnxt.le) (logn_two n hn)
    (by exact_mod_cast (show 0 < r by omega)) (certificate r hr)⟩

#print axioms all_parameters
end Superperm86


namespace Superperm86
/-- At the last size before parameter 7 is admissible, the 85 version of the
scalar certificate fails. This only concerns the 26/r construction estimate. -/
theorem coefficient85_obstruction :
    let n := thresh 7 - 1
    thresh 6 ≤ n ∧ n < thresh 7 ∧
      (85*(6:ℝ))^20 * (Real.log (n:ℝ))^2 < 26^20*(n:ℝ) := by
  dsimp only
  constructor
  · decide
  constructor
  · decide
  have hn0 : (0:ℝ) < (thresh 7 - 1:ℕ) := by exact_mod_cast (by decide : 0 < thresh 7 - 1)
  have hn : ((thresh 7 - 1:ℕ):ℝ) ≤ 2^99 := by exact_mod_cast (by decide : thresh 7-1 ≤ 2^99)
  have hlog := Real.log_le_log hn0 hn
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hlo := logn_two (thresh 7 - 1) (by decide)
  have hh : Real.log ((thresh 7 - 1:ℕ):ℝ) ≤ 70 := by linarith only [hlog, Real.log_two_lt_d9]
  have hsq := pow_le_pow_left₀ (show 0 ≤ Real.log ((thresh 7 - 1:ℕ):ℝ) by linarith only [hlo]) hh 2
  apply (mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ (85*(6:ℝ))^20)).trans_lt
  exact_mod_cast (by decide : (85*6)^20 * 70^2 < 26^20 * (thresh 7 - 1))
#print axioms coefficient85_obstruction
end Superperm86

namespace CoefficientTwoPrecision.Asym22
open Asym35

/-- Quantitative upper bound, with an actual superpermutation as witness. -/
theorem word_rate86 (n : ℕ) (hn : logThreshold 6 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℝ) ≤ (SuperpermutationBounds.F3 n : ℝ) +
        (2 + 86*(Real.log n)^(1/10:ℝ)*(n:ℝ)^(-1/20:ℝ)) * ((n-4).factorial:ℝ) := by
  obtain ⟨r,hr,hok,hs⟩ := Superperm86.all_parameters n hn
  have hr0 : 0 < r := by omega
  obtain ⟨w, hw, hwlen⟩ := finite_covering_word_log n r hr hok
  have hlen := (integer_bound_iff35 n r hr0 w).1 hwlen
  have hcast := (Rat.cast_le (K:=ℝ)).2 hlen
  push_cast at hcast
  have hmul := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) (n-4).factorial)
  refine ⟨w,hw,?_⟩
  linarith only [hcast,hmul]

/-- Two-sided explicit estimate for the actual shortest length, on the same domain. -/
theorem shortest_rate86 (n : ℕ) (hn : logThreshold 6 ≤ n) :
    |(ConstAsym.L n:ℝ) - (SuperpermutationBounds.F3 n:ℝ) - 2*((n-4).factorial:ℝ)| ≤
      86*(Real.log n)^(1/10:ℝ)*(n:ℝ)^(-1/20:ℝ)*((n-4).factorial:ℝ) := by
  obtain ⟨w,hw,hu⟩ := word_rate86 n hn
  have hmin : (ConstAsym.L n:ℝ) ≤ (w.length:ℝ) := by exact_mod_cast ConstAsym.L_le_length hw
  have h256 := logThreshold_six_ge n hn
  have hlo := ConstAsym.lower2_ratio (show 7 ≤ n by omega)
  have hf : (0:ℝ) < ((n-4).factorial:ℝ) := by positivity
  have hlow : 2 - 2 / ((n:ℝ)-4) ≤
      ((ConstAsym.L n:ℝ) - (SuperpermutationBounds.F3 n:ℝ)) / ((n-4).factorial:ℝ) := by
    exact_mod_cast hlo
  have hlow' := (le_div_iff₀ hf).mp hlow
  have hl := lower_error_log_bound n h256
  have hlog := Superperm86.logn_two n hn
  have hp : 0 ≤ (Real.log n)^(1/10:ℝ)*(n:ℝ)^(-1/20:ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hm := mul_le_mul_of_nonneg_right (show 2/((n:ℝ)-4) ≤
      86*(Real.log n)^(1/10:ℝ)*(n:ℝ)^(-1/20:ℝ) by linarith only [hl,hp]) hf.le
  exact abs_le.mpr ⟨by linarith only [hlow',hm], by linarith only [hmin,hu]⟩

#print axioms word_rate86
#print axioms shortest_rate86
end CoefficientTwoPrecision.Asym22
