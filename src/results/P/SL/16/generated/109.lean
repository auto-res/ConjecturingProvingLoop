

theorem Topology.interior_union_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `A ⊆ A ∪ B`, hence `interior A ⊆ interior (A ∪ B)`
      have h_subset : interior A ⊆ interior (A ∪ B) := by
        have hA_sub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hA_sub
      exact h_subset hxA
  | inr hxB =>
      -- `B ⊆ A ∪ B`, hence `interior B ⊆ interior (A ∪ B)`
      have h_subset : interior B ⊆ interior (A ∪ B) := by
        have hB_sub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hB_sub
      exact h_subset hxB