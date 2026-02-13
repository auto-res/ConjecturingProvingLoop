

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : (interior A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hA
  | inr hB =>
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : (interior B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_right
        exact this
      exact hsubset hB