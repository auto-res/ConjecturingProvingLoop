

theorem interior_diff_subset_closure_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ closure A := by
  intro x hx
  -- From `x ∈ interior (A \ B)` we obtain `x ∈ A \ B`.
  have h_mem : x ∈ A \ B := interior_subset hx
  -- Hence `x ∈ A`.
  have hxA : x ∈ A := h_mem.1
  -- Since `A ⊆ closure A`, we conclude `x ∈ closure A`.
  exact subset_closure hxA