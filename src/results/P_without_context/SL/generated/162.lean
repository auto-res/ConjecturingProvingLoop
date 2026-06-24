

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2
  have hSub : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using (interior_subset (s := closure (interior A)))
  exact Set.Subset.trans hP2 hSub