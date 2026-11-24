module

public import TightBound
public import alternation.AlternatingActualReturn
@[expose] public section
namespace GeneralAlt
open SuperpermutationLowerBound SuperpermutationLowerBound.Refinement
open SuperpermutationLowerBound.Refinement.ChainReturns

abbrev publicReturn (m : ℕ) := SuperpermutationBounds.ChainReturns.returnZero (3*m)

theorem public_both (m : ℕ) (hm : 3 ≤ m) : Both m (publicReturn m) := by
  intro hk P hP segment
  let R := publicReturn m
  have hR : 0 < R := SuperpermutationBounds.ChainReturns.returnZero_pos (by omega)
  have hn : 7 ≤ 3*m := by omega
  have hp := alternating_pair_power m hm hn
  have hp' : (cellRho (3*m) hn * (cellG (3*m) hn) ^ (2*m-1) *
      cellRho (3*m) hn * (cellG (3*m) hn) ^ (2*m-2)) ^ R = 1 := by
    have hh := reversed_pair_return
      (cellRho (3*m) hn * (cellG (3*m) hn) ^ (2*m-1))
      (cellRho (3*m) hn * (cellG (3*m) hn) ^ (2*m-2)) R
      (by simpa only [mul_assoc] using hp)
    simpa only [mul_assoc] using hh
  constructor
  · exact actual_periodic_pair_avoidance (3*m) hn P hP segment (2*m-1) (2*m-2) R
      (by omega) (by omega) hR hp
  · exact actual_periodic_pair_avoidance (3*m) hn P hP segment (2*m-2) (2*m-1) R
      (by omega) (by omega) hR hp'

theorem word_general (m : ℕ) (hm : 3 ≤ m)
    (w : List (Fin (3*m+1))) (hw : SuperpermutationBounds.Covers w) :
    SuperpermutationLowerBound.ChainReturns.bound (3*m+1)
      (tightP m (publicReturn m)) (tightT m (publicReturn m)) ≤ w.length :=
  tight_word hm (SuperpermutationBounds.ChainReturns.returnZero_pos (by omega)) (public_both m hm) w hw

#print axioms word_general
end GeneralAlt
