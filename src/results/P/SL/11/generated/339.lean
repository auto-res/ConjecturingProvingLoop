

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntA =>
      -- Step 1: `interior A ⊆ interior (A ∪ B)`.
      have h₁ : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_left
      -- Step 2: `interior (A ∪ B) ⊆ interior (closure (A ∪ B))`.
      have h₂ : interior (A ∪ B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact subset_closure
      exact h₂ (h₁ hIntA)
  | inr hIntB =>
      -- The argument is symmetric for `interior B`.
      have h₁ : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_right
      have h₂ : interior (A ∪ B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact subset_closure
      exact h₂ (h₁ hIntB)