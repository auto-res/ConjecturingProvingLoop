

theorem closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have hSub : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hSub
      exact hIncl hA
  | inr hB =>
      have hIncl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have hSub : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hSub
      exact hIncl hB