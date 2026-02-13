

theorem isOpen_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure A) := interior_mono subset_closure
  simpa [hA.interior_eq] using h