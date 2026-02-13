

theorem Topology.closed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    Topology.P1 (X:=X) A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P2_implies_isOpen (X:=X) (A:=A) hA_closed hP2
  exact Topology.isOpen_subset_closureInterior (X:=X) (A:=A) hA_open