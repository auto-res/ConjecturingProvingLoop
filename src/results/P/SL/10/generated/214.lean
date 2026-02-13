

theorem Topology.closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) ⊆ closure A := by
  exact closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)