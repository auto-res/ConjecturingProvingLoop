

theorem closure_inter_closure_subset_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) := by
  -- The set `A ∩ closure B` is obviously contained in `A`.
  have hSub : (A ∩ closure (B : Set X) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono hSub