

theorem frontier_closure_eq_empty_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (closure A) = (∅ : Set X) := by
  intro hDense
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [h_closure_univ, frontier_univ_eq_empty (X := X)]