

theorem Topology.P1_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (A : Set X)) : Topology.P1 A := by
  -- The given equality shows that `A` is open.
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using this
  -- Every open set satisfies `P1`.
  exact Topology.IsOpen_P1 (A := A) hOpen