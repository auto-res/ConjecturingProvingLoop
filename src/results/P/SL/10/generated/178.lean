

theorem Topology.closure_interior_eq_of_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  -- From `hP3` and the closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Hence `interior A = A`.
  have h_int : interior A = A := hOpen.interior_eq
  -- Rewrite and simplify.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hClosed.closure_eq