

theorem Topology.P2_of_interiorClosure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) : Topology.P2 (A := A) := by
  -- From the hypothesis we immediately obtain that `A` is open.
  have hA_open : IsOpen A := by
    simpa [h] using (isOpen_interior : IsOpen (interior (closure A)))
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hA_open