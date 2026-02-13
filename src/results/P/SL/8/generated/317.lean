

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure B := by
  have h : A ∩ B ⊆ B := Set.inter_subset_right
  exact closure_mono h