

theorem frontier_eq_empty_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    frontier A = (∅ : Set X) := by
  have hInt : interior A = A := hAopen.interior_eq
  have hClos : closure A = A := hAclosed.closure_eq
  calc
    frontier A = closure A \ interior A := by
      simpa using frontier_eq_closure_diff_interior (X := X) (A := A)
    _ = A \ interior A := by
      simpa [hClos]
    _ = A \ A := by
      simpa [hInt]
    _ = (∅ : Set X) := by
      simp