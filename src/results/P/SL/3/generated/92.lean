

theorem P1_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  exact P1_of_isOpen (A := A) hOpen