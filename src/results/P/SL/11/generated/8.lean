

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  simpa [hA.interior_eq] using hsubset