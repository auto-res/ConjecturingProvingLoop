

theorem dense_frontier_eq_compl_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
  intro hDense
  -- For a dense set, its closure is the whole space.
  have h_closure : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Rewrite the frontier via the standard characterization.
  have h_frontier : frontier A = closure A \ interior A := by
    simpa using (frontier_eq_closure_diff_interior (X := X) (A := A))
  -- Substitute `closure A = univ` into the expression.
  simpa [h_closure] using h_frontier