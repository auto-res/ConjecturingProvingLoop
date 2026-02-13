

theorem frontier_closure_eq_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) = closure A \ interior (closure A) := by
  simpa [frontier_eq_closure_diff_interior, closure_closure]