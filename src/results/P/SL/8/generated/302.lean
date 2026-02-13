

theorem closure_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A := by
  have h : A ∩ B ⊆ A := Set.inter_subset_left
  exact closure_mono h