

theorem Topology.frontier_union_subset_closure_frontier_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ closure (frontier A ∪ frontier B) := by
  intro x hx
  have hx_union : x ∈ frontier A ∪ frontier B :=
    (Topology.frontier_union_subset (A := A) (B := B)) hx
  exact subset_closure hx_union