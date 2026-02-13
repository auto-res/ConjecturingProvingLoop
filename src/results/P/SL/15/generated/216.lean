

theorem interior_closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  -- The density of `A` gives `closure A = univ`.
  have hClosure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewrite using `hClosure` and evaluate with `simp`.
  simpa [hClosure, closure_univ, interior_univ]