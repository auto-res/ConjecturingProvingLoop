

theorem P3_of_isClosed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  exact Topology.P1_of_isOpen (A := A) hOpen