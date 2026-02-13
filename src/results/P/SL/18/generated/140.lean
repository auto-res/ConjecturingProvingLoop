

theorem interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is contained in `interior (A ∪ B)`
      have hIncl : interior (A : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hxA
  | inr hxB =>
      -- `interior B` is contained in `interior (A ∪ B)`
      have hIncl : interior (B : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hxB