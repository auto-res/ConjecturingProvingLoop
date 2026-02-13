

theorem interior_eq_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A → Topology.P2 A := by
  intro hInt
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  -- Open sets satisfy the `P2` property.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen