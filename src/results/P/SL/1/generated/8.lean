

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  simpa [hA.interior_eq] using h