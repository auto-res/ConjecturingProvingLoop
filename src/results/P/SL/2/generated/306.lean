

theorem Topology.frontier_eq_empty_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P1 A := by
  intro hFrontier
  have hSubset : frontier (A : Set X) ⊆ closure (interior A) := by
    simpa [hFrontier] using (Set.empty_subset _)
  exact
    Topology.P1_of_frontier_subset_closure_interior (A := A) hSubset