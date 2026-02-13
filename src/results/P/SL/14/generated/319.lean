

theorem Topology.P2_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P2 A := by
  -- A closed, dense set is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen