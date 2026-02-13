

theorem P3_iff_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) ↔ interior A = A := by
  constructor
  · intro hP3
    exact interior_eq_self_of_P3_closed (A := A) hA hP3
  · intro hIntEq
    -- `A` is open because it coincides with its interior.
    have hOpen : IsOpen (A : Set X) := by
      simpa [hIntEq] using (isOpen_interior : IsOpen (interior (A : Set X)))
    -- Open sets satisfy `P3`.
    simpa [hIntEq] using Topology.open_satisfies_P3 (A := A) hOpen