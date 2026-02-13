

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure (B : Set X) := by
  exact closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)