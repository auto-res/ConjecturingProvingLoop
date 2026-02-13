

theorem closure_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure B ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- `closure A ⊆ closure (A ∪ B)` via monotonicity of `closure`.
      have hIncl : closure (A : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hAx
  | inr hBx =>
      -- Symmetric argument for `closure B`.
      have hIncl : closure (B : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hBx