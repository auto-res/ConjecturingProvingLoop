

theorem closed_P2_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hA_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  simpa using hA_open.interior_eq