

theorem Topology.P3_of_interiorClosure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) : Topology.P3 (A := A) := by
  -- From the hypothesis we deduce that `A` is open.
  have h_open : IsOpen A := by
    simpa [h] using (isOpen_interior : IsOpen (interior (closure A)))
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) h_open