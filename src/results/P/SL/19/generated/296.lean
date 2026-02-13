

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) ⊆ closure A := by
  -- `frontier A` is closed, so its closure is itself.
  have hEq : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- The frontier of `A` is always contained in `closure A`.
  have hSubset : (frontier A : Set X) ⊆ closure A :=
    Topology.frontier_subset_closure (A := A)
  -- Combine the two facts.
  simpa [hEq] using hSubset