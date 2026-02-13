

theorem frontier_eq_closure_diff_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    frontier A = closure A \ A := by
  have h := frontier_eq_closure_diff_interior (X := X) (A := A)
  simpa [hA.interior_eq] using h