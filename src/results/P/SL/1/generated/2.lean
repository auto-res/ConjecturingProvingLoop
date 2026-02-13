

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    (by
      have hsubset : interior A ⊆ closure (interior A) := by
        intro x hx
        exact subset_closure hx
      have hmono : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono hsubset
      simpa [interior_interior] using hmono)