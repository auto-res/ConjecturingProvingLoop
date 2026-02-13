

theorem Topology.P1_iff_closure_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_isClosed_of_P1 hA hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    simpa [hEq] using hx