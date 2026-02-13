

theorem closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hIncl :
          closure (interior (A : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hAx
  | inr hBx =>
      have hIncl :
          closure (interior (B : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hBx