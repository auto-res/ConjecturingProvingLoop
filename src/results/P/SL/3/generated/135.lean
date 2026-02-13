

theorem interior_eq_self_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  simpa using hOpen.interior_eq