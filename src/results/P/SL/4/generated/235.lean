

theorem frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier A ⊆ closure A := by
  intro x hx
  -- By definition, `x ∈ frontier A` means `x ∈ closure A` and `x ∉ interior A`.
  exact hx.1