

theorem isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  have h_subset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure
  exact h_subset hx_int