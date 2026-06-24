

theorem isOpen_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  have hInt : interior A = A := hA.interior_eq
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    have hsub : interior A ⊆ closure (interior A) := subset_closure
    exact interior_maximal hsub isOpen_interior
  simpa [hInt] using hsubset