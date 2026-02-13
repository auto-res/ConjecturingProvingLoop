

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
  -- Since `A ∩ B ⊆ B`, applying `closure_mono` gives the desired inclusion.
  have hSub : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro x hx
    exact hx.2
  exact closure_mono hSub