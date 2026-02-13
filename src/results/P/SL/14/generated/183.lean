

theorem Topology.interior_eq_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hP3
  -- For an open set, the interior equals the set itself.
  simpa using hOpen.interior_eq