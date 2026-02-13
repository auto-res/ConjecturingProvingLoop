

theorem Topology.boundary_eq_univ_of_dense_and_emptyInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense (A : Set X))
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    closure (A : Set X) \ interior A = (Set.univ : Set X) := by
  -- The density of `A` says that `closure A = univ`.
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Substitute both equalities and simplify.
  simpa [h_cl, hInt]