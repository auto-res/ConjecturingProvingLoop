

theorem isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa using hsubset