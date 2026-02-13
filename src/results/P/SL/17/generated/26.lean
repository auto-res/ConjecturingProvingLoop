

theorem Topology.interior_eq_self_of_closed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hOpen : IsOpen A := Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  simpa using hOpen.interior_eq