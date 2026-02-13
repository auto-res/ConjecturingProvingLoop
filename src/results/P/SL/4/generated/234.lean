

theorem interior_closure_interior_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    interior (closure (interior A)) = A := by
  have hInt : interior A = A := hAopen.interior_eq
  calc
    interior (closure (interior A))
        = interior (closure A) := by
          simpa [hInt]
    _ = A := by
          simpa using
            interior_closure_eq_of_clopen (A := A) hAopen hAclosed