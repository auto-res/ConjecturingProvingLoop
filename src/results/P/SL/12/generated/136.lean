

theorem Topology.isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    IsOpen (A : Set X) := by
  exact
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP2