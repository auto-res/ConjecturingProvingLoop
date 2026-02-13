

theorem closure_inter_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∩ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  rcases hx with ⟨hxA, _hxB⟩
  -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields
  -- `closure A ⊆ closure (A ∪ B)`, and hence the desired membership.
  have hSub : A ⊆ A ∪ B := fun y hy => Or.inl hy
  have hCl : closure A ⊆ closure (A ∪ B) := closure_mono hSub
  exact hCl hxA