

theorem closure_union_interior_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∪ interior (B : Set X)) : Set X) ⊆
      closure (A ∪ B : Set X) := by
  -- First, note that `A ∪ interior B ⊆ A ∪ B`.
  have hSub : ((A ∪ interior (B : Set X)) : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl hxA
    | inr hxIntB =>
        exact Or.inr (interior_subset hxIntB)
  -- Taking closures preserves inclusions.
  exact closure_mono hSub