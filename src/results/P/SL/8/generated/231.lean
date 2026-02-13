

theorem interior_union_subset_interiorUnion {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is monotone with respect to inclusion.
      have h_subset : A ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      have h_incl : interior A ⊆ interior (A ∪ B) := interior_mono h_subset
      exact h_incl hxA
  | inr hxB =>
      -- Symmetric argument for `interior B`.
      have h_subset : B ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      have h_incl : interior B ⊆ interior (A ∪ B) := interior_mono h_subset
      exact h_incl hxB