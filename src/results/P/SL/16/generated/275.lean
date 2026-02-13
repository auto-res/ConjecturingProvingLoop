

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  -- `A ⊆ A ∪ B`
  have hA : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Hence `closure A ⊆ closure (A ∪ B)`
  have hCl : closure A ⊆ closure (A ∪ B) := closure_mono hA
  -- Apply monotonicity of `interior`
  exact interior_mono hCl