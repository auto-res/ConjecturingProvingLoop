

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : interior (closure A) = (Set.univ : Set X) := by
  have h_closure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]