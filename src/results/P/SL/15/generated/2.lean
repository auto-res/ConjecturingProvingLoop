

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have hInt : x ∈ interior A := by
    simpa [IsOpen.interior_eq hA] using hx
  exact subset_closure hInt