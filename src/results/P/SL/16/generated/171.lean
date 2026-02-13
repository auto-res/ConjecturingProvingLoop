

theorem Topology.interior_eq_self_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hInt : interior A = A) :
    Topology.P1 (X := X) A ∧
      Topology.P2 (X := X) A ∧
      Topology.P3 (X := X) A := by
  -- From `interior A = A`, deduce that `A` is open.
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using this
  -- Any open set satisfies all three properties.
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen