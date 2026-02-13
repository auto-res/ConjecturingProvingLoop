

theorem closure_interior_eq_self_of_closed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- From `P2` and closedness of `A`, we have `interior A = A`.
  have hIntEq : interior A = A :=
    (Topology.P2_closed_iff_interior_eq (A := A) hClosed).1 hP2
  calc
    closure (interior A) = closure A := by
      simpa [hIntEq]
    _ = A := hClosed.closure_eq