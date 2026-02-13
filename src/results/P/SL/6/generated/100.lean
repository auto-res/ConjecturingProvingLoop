

theorem interior_eq_self_of_P2_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → interior A = A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P2_iff_open_of_closed (A := A) hA).1 hP2
  simpa using hOpen.interior_eq