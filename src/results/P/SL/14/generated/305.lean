

theorem Topology.P3_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P3 A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen