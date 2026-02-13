

theorem frontier_eq_closure_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  have h := (frontier_eq_closure_diff_interior (X := X) (A := A))
  simpa [hInt, Set.diff_empty] using h