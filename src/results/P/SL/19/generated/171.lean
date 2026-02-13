

theorem Topology.closure_inter_frontier_eq_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ frontier A = frontier A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxFr
    exact And.intro hxFr.1 hxFr