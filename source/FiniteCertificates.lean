import TightBound
import Geometry13
import Geometry16

namespace EarlyAlternation
open SuperpermutationLowerBound.Refinement

theorem lower_thirteen (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) :
    6746626690 ≤ w.length := by
  apply GeneralAlt.tight13 _ w hw
  intro hk P hP s
  exact ⟨Early13.miss0 s, Early13.miss1 s⟩

theorem lower_sixteen (w : List (Fin 16)) (hw : SuperpermutationBounds.Covers w) :
    22318554323969 ≤ w.length := by
  apply GeneralAlt.tight16 _ w hw
  intro hk P hP s
  exact ⟨Early16.miss0 s, Early16.miss1 s⟩

#print axioms lower_thirteen
#print axioms lower_sixteen
end EarlyAlternation
