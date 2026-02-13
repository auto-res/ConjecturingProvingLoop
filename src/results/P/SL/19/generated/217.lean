

theorem Topology.frontier_union_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∪ B) ⊆ closure A ∪ closure B := by
  intro x hx
  have : (x : X) ∈ closure (A ∪ B) := hx.1
  simpa [closure_union] using this