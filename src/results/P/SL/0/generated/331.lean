

theorem closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ B) ⊆ closure (A ∪ B : Set X) := by
  -- First, show the required subset relation before taking closures.
  have hSub :
      ((interior (A : Set X)) ∪ B : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hxIntA => exact Or.inl (interior_subset hxIntA)
    | inr hxB    => exact Or.inr hxB
  -- Taking closures preserves inclusions.
  exact closure_mono hSub