

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  have hSub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans hA hSub