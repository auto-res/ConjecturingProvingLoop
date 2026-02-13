

theorem Topology.closure_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B) := by
  -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields the result.
  have h_subset : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  exact closure_mono h_subset