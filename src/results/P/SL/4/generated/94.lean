

theorem closure_interior_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    closure (interior A) = A := by
  have hInt : interior A = A := hAopen.interior_eq
  have hCl : closure A = A := hAclosed.closure_eq
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := hCl