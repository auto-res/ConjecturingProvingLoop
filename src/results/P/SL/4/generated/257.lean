

theorem frontier_eq_self_of_closed_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hInt : interior A = (∅ : Set X)) :
    frontier A = A := by
  have h := frontier_eq_diff_interior_of_closed (X := X) (A := A) hA_closed
  simpa [hInt] using h