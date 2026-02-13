

theorem P1_closed_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_closed_P1 (A := A) hA hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure (interior A) := by
      simpa [hEq] using hx
    exact this