

theorem closure_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
  -- The set `A ∩ B` is contained in `A`.
  have hSub : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  -- Taking closures preserves this inclusion.
  exact closure_mono hSub