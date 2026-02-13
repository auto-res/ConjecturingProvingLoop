

theorem interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
  -- First, note the basic inclusion `A ⊆ A ∪ B`.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Lift this inclusion through `closure`.
  have hClSub : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono hClSub