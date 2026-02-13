

theorem Topology.interior_inter_subset_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior B := by
  exact interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)