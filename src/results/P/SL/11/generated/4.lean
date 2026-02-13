

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : A ⊆ closure A)
  simpa [hA.interior_eq] using hsubset