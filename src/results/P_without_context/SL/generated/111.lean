

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact Set.Subset.trans h h'