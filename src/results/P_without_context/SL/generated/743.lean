

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  have hInt : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact Set.Subset.trans hP2 hInt