

theorem Topology.P1_iff_closure_interior_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_closed_of_P1 (A := A) hA_closed hP1
  · intro h_eq
    unfold Topology.P1
    intro x hx
    simpa [h_eq] using hx