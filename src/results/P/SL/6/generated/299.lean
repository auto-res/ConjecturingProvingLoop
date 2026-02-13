

theorem interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  -- First, note the obvious inclusion `B ⊆ A ∪ B`.
  have hSub : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  have hClSub : closure (B : Set X) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono hClSub