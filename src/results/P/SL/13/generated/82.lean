

theorem Topology.P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hPA : Topology.P3 (X:=X) A) (hPB : Topology.P3 (X:=X) B) :
    Topology.P3 (X:=X) (A ∩ B) := by
  -- Both sets are open because they are closed and satisfy P3
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hPA
  have hB_open : IsOpen (B : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=B) hB_closed hPB
  -- The intersection of two open sets is open
  have h_inter_open : IsOpen ((A ∩ B) : Set X) := hA_open.inter hB_open
  -- Open sets always satisfy P3
  exact Topology.isOpen_subset_interiorClosure (X:=X) (A:=A ∩ B) h_inter_open