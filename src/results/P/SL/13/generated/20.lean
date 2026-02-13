

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP3
    exact Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  · intro hA_open
    exact Topology.isOpen_subset_interiorClosure (X:=X) (A:=A) hA_open