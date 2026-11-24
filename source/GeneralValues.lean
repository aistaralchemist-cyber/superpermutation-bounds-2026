import GeneralLower

namespace GeneralAlt.Uniform

/-- Direct evaluation of the closed expression, with natural-number ceilings. -/
theorem closed_values_through_fourteen :
    (List.range 14).map (fun k => closedLower (k + 1)) =
      [1, 3, 9, 33, 153, 870, 5895, 46130, 408469, 4033375,
       43917903, 522622380, 6746626690, 93891141149] := by decide +kernel

#print axioms closed_values_through_fourteen
end GeneralAlt.Uniform
