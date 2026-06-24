

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
  exact fun x hx => hsubset (hP2 hx)