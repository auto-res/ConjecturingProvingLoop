

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  exact
    Set.Subset.trans hP2
      (by
        simpa using interior_subset (s := closure (interior A)))