

theorem Topology.isClosed_iff_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ frontier A ⊆ A := by
  constructor
  · intro hClosed
    exact Topology.frontier_subset_of_isClosed (A := A) hClosed
  · intro hSubset
    exact Topology.isClosed_of_frontier_subset (A := A) hSubset