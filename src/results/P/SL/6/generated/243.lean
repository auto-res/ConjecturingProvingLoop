

theorem P1_of_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = A) : Topology.P1 A := by
  -- From the hypothesis we infer that `A` is open.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Open sets satisfy `P1`.
  exact Topology.open_satisfies_P1 (A := A) hOpen