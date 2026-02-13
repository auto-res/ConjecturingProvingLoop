

theorem interior_eq_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = A) : Topology.P1 A := by
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior A))
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen