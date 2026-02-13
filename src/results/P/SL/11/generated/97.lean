

theorem interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_left
      exact hsubset hA
  | inr hB =>
      have hsubset : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_right
      exact hsubset hB