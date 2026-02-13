

theorem frontier_univ_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  simpa [frontier_eq_closure_diff_interior, closure_univ, interior_univ]