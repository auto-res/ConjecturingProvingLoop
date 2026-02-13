

theorem Topology.closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B) := by
  exact closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)