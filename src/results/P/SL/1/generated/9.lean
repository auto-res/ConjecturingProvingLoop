

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  simpa [hA.interior_eq] using h