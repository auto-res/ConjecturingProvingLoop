

theorem P3_implies_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → (A ⊆ closure A) := by
  intro hA
  dsimp [Topology.P3] at hA
  exact hA.trans (interior_subset : interior (closure A) ⊆ closure A)