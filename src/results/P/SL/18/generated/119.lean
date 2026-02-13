

theorem closure_interior_eq_self_of_closed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A := (Topology.P3_closed_iff_open hClosed).1 hP3
  -- Hence the interior of `A` is `A` itself.
  have hInt : interior A = A := hOpen.interior_eq
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := hClosed.closure_eq