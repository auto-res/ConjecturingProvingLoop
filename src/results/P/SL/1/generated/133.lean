

theorem Topology.interior_closure_eq_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior (closure A) = A := by
  -- From `P3` and closedness we get that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.isOpen_of_P3_of_isClosed (A := A) hA_closed) hP3
  -- The interior of an open set is itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- The closure of a closed set is itself.
  have hCl : closure A = A := hA_closed.closure_eq
  -- Combine the two equalities.
  simpa [hCl, hInt]