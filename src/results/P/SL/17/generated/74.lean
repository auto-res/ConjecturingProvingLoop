

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact Topology.interior_eq_self_of_closed_and_P3 (A := A) hA_closed hP3
  · intro h_int
    -- From `interior A = A`, we get that `A` is open.
    have hA_open : IsOpen A := by
      simpa [h_int] using (isOpen_interior : IsOpen (interior A))
    -- Every open set satisfies `P3`.
    simpa using (Topology.P3_of_isOpen (A := A) hA_open)