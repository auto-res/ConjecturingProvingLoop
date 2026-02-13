

theorem Topology.interior_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A := by
  exact interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)