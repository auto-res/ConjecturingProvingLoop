

theorem interior_eq_self_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  simpa using hOpen.interior_eq