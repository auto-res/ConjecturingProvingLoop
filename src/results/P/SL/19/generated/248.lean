

theorem Topology.frontier_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  simpa [Set.diff_eq, frontier_compl] using
    (Topology.frontier_inter_subset (A := A) (B := Bᶜ))