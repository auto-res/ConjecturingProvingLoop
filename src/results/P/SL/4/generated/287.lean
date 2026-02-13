

theorem frontier_eq_univ_of_dense_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior A = (∅ : Set X) → frontier (A : Set X) = (Set.univ : Set X) := by
  intro hDense hInt
  -- Use the previously established description of the frontier of a dense set.
  have h :=
    dense_frontier_eq_compl_interior (X := X) (A := A) hDense
  -- Substitute the hypothesis `interior A = ∅` and simplify.
  simpa [hInt, Set.diff_empty] using h