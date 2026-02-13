

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) := by
  dsimp [Topology.P2]
  intro x hxA
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa [hA.interior_eq] using h_subset hxA