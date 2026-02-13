

theorem Topology.P3_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    Topology.P3 A := by
  -- A closed set with dense interior is open (from the existing lemma).
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_denseInterior
      (X := X) (A := A) hA_closed hDense
  -- Every open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen