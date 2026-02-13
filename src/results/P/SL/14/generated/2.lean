

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa [hA.interior_eq] using hsubset