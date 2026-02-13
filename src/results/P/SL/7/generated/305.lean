

theorem Topology.interiorClosure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure A) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C)) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          have hSub : interior (closure A) ⊆ interior (closure (A ∪ B ∪ C)) := by
            apply interior_mono
            apply closure_mono
            intro y hy
            exact Or.inl (Or.inl hy)
          exact hSub hA
      | inr hB =>
          have hSub : interior (closure B) ⊆ interior (closure (A ∪ B ∪ C)) := by
            apply interior_mono
            apply closure_mono
            intro y hy
            exact Or.inl (Or.inr hy)
          exact hSub hB
  | inr hC =>
      have hSub : interior (closure C) ⊆ interior (closure (A ∪ B ∪ C)) := by
        apply interior_mono
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact hSub hC