

theorem P2_iff_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) ↔ interior A = A := by
  constructor
  · intro hP2
    exact (interior_eq_self_of_P2_closed (A := A) hA) hP2
  · intro hIntEq
    exact P2_of_interior_eq_self (A := A) hIntEq