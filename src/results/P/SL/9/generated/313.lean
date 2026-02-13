

theorem Topology.frontier_frontier_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier (A : Set X)) ⊆ frontier A := by
  intro x hx
  have hx_cl : x ∈ closure (frontier (A : Set X)) := hx.1
  have h_cl_eq :
      closure (frontier (A : Set X)) = frontier (A : Set X) :=
    (isClosed_frontier : IsClosed (frontier (A : Set X))).closure_eq
  simpa [h_cl_eq] using hx_cl