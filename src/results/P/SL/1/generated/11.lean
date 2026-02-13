

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  dsimp [Topology.P2]
  have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  have hmono :
      interior (interior (closure A)) ⊆ interior (closure (interior (closure A))) :=
    interior_mono hsubset
  simpa [interior_interior] using hmono