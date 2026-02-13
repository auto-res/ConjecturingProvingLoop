

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set difference `A \ B` is obviously contained in `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset