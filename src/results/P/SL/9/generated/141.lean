

theorem Topology.interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : interior A ⊆ interior (A ∪ B) := by
        have hAB : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hAB
      exact h_subset hxA
  | inr hxB =>
      have h_subset : interior B ⊆ interior (A ∪ B) := by
        have hAB : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hAB
      exact h_subset hxB