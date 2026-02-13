

theorem interior_eq_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A → Topology.P3 A := by
  intro hIntEq
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [hIntEq] using (isOpen_interior : IsOpen (interior A))
  -- Open sets satisfy `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen