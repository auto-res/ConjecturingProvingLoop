

theorem frontier_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simpa [frontier_eq_closure_diff_interior]