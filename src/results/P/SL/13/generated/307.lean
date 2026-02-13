

theorem Topology.closureInterior_eq_univ_of_P2_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X := X) A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  -- From `P2` we have equality of the two closures.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closureInterior (X := X) (A := A) hP2
  -- Density of `A` tells us its closure is the whole space.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h_closureA] using h_eq.symm