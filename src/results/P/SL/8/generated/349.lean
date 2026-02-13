

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (A ∪ B) := by
  -- The set `A` is contained in `A ∪ B`.
  have h : A ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono h