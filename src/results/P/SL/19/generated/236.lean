

theorem Topology.frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (frontier A) ⊆ closure A := by
  intro x hx
  have h_front : x ∈ frontier A :=
    (Topology.frontier_frontier_subset_frontier (A := A)) hx
  exact (Topology.frontier_subset_closure (A := A)) h_front