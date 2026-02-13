

theorem Topology.frontier_frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (frontier A) ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  have hxFrontA : x ∈ frontier A :=
    (Topology.frontier_frontier_subset_frontier (A := A)) hx
  exact (Topology.frontier_subset_closure_inter_closure_compl (A := A)) hxFrontA