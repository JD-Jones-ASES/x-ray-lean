import Solution

namespace XRay.Controls

-- Two loops: each contributes two incidences at its own vertex.
example : DegreeTwo (fun i : Fin 2 => i) (fun i => i) := by unfold DegreeTwo incidence; decide

-- Two parallel edges between the two vertices.
example : DegreeTwo (fun _ : Fin 2 => 0) (fun _ => 1) := by unfold DegreeTwo incidence; decide

-- A missing incidence is rejected.
example : ¬ DegreeTwo (fun _ : Fin 2 => 0) (fun _ => 0) := by unfold DegreeTwo incidence; decide

-- Repeated labels are retained by the matrix equivalence.
example : Realizable (![2, 2] : Profile 2) := by
  apply realizable_of_integer_margins ![1, 2] ![2, 1]
  · rw [board_eq_indices]; decide
  · rw [board_eq_indices]; decide
  · decide

-- Reflection reverses and negates rank deviations.
example : reflect (![2, 3, 4] : Profile 3) = ![2, 3, 4] := by decide

end XRay.Controls
