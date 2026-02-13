

theorem Topology.isOpen_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    IsOpen A := by
  -- From density of `interior A`, we obtain `P2 A`.
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  -- A closed set satisfying `P2` is open.
  exact Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2