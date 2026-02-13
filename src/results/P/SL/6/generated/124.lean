

theorem P2_of_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = A) : Topology.P2 (A : Set X) := by
  -- `interior A` is open, so `A` is open by the given equality.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Open sets satisfy `P2`.
  exact Topology.open_satisfies_P2 (A := A) hOpen