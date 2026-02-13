

theorem frontier_eq_diff_interior_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A = A \ interior A := by
  have h := frontier_eq_closure_diff_interior (X := X) (A := A)
  simpa [hA.closure_eq] using h