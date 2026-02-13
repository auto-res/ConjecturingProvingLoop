

theorem frontier_interior_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = closure (interior A) \ interior A := by
  simpa [interior_interior]
    using
      (frontier_eq_closure_diff_interior (X := X) (A := interior A))