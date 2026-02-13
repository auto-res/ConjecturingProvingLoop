

theorem Topology.P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hxA
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  exact subset_closure hxInt