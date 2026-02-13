

theorem Topology.interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- From the density of `interior A` we already know `closure A = univ`.
  have h_closure_univ :
      closure (A : Set X) = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (X := X) (A := A) hA
  -- Rewrite and simplify using `interior_univ`.
  simpa [h_closure_univ, interior_univ]