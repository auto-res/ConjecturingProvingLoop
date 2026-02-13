

theorem interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior (B : Set X))) ⊆
      interior (closure (interior (A ∪ B : Set X))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B : Set X))) := by
        apply interior_mono
        have hSub :
            closure (interior (A : Set X)) ⊆
              closure (interior (A ∪ B : Set X)) := by
          apply closure_mono
          have hIntSub :
              interior (A : Set X) ⊆ interior (A ∪ B : Set X) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact hIntSub
        exact hSub
      exact hIncl hA
  | inr hB =>
      have hIncl :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B : Set X))) := by
        apply interior_mono
        have hSub :
            closure (interior (B : Set X)) ⊆
              closure (interior (A ∪ B : Set X)) := by
          apply closure_mono
          have hIntSub :
              interior (B : Set X) ⊆ interior (A ∪ B : Set X) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact hIntSub
        exact hSub
      exact hIncl hB