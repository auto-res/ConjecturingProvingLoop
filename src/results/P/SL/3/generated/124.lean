

theorem Set.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_sub : interior (A : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_sub hA
  | inr hB =>
      have h_sub : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_sub hB