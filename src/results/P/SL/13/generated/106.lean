

theorem Topology.closed_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P2 (X := X) A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_dense_isOpen (X := X) (A := A) hA_closed hA_dense
  exact isOpen_implies_P2 (X := X) (A := A) hA_open