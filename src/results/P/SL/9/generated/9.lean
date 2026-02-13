

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  have hxIntA : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hxIntA