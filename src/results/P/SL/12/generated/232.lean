

theorem Topology.isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    IsOpen (A : Set X) := by
  exact
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP3