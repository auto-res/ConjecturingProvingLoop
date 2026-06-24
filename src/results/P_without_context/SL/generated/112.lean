

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P2, Topology.P1] at h ⊢
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact Set.Subset.trans h h₁