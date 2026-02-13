

theorem closure_frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = closure A \ interior A := by
  calc
    closure (frontier A)
        = frontier A := by
          simpa using
            (closure_frontier_eq_frontier (X := X) (A := A))
    _   = closure A \ interior A := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := A))