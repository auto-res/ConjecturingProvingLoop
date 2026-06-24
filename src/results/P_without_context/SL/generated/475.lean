

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro h
  dsimp [Topology.P2, Topology.P1] at h ⊢
  exact Set.Subset.trans h (interior_subset (s := closure (interior A)))