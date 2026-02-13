

theorem denseInterior_implies_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 (closure (interior A)) := by
  -- From the density of `interior A`, we know that its closure is open.
  have hOpen : IsOpen (closure (interior A)) :=
    isOpen_closure_interior_of_denseInterior (X := X) (A := A) hDense
  -- For a closed set, `P2` is equivalent to openness.
  exact
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
        (X := X) (A := A)).2 hOpen