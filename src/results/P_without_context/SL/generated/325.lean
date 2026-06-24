

theorem isOpen_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  have hInt : interior A = A := hA.interior_eq
  have hIncl : interior A ⊆ interior (closure A) := interior_mono subset_closure
  simpa [hInt] using hIncl