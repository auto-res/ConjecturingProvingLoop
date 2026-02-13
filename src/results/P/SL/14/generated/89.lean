

theorem Topology.interior_eq_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- For an open set, the interior equals the set itself.
  simpa using hOpen.interior_eq