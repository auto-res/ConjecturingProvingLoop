

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hA
  have hsubs : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
  exact Set.Subset.trans hA hsubs