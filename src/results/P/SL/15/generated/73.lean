

theorem dense_closure_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  have h : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h, interior_univ, closure_univ]