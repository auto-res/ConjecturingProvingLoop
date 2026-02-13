

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior (closure A) = (Set.univ : Set X) := by
  intro hDense
  have h_closure : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [h_closure, interior_univ]