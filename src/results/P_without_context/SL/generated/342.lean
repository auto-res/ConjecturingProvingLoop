

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hSub : A ⊆ closure (interior A) :=
    Set.Subset.trans hP2 (by
      simpa using interior_subset)
  simpa [Topology.P1] using hSub