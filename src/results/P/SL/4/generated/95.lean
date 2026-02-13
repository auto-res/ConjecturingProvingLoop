

theorem interior_closure_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    interior (closure A) = A := by
  -- Since `A` is closed, its closure equals itself.
  have hClosure : closure A = A := hAclosed.closure_eq
  -- Since `A` is open, its interior equals itself.
  have hInterior : interior A = A := hAopen.interior_eq
  -- Combine the two equalities to reach the goal.
  calc
    interior (closure A) = interior A := by
      simpa [hClosure]
    _ = A := by
      simpa [hInterior]