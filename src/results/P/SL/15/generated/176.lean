

theorem interior_closure_interior_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  have h_closure : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]