

theorem union_three_interiors_subset_interior_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X) ∪ interior (C : Set X)) ⊆
      interior (A ∪ B ∪ C : Set X) := by
  intro x hx
  -- Split the triple union into cases.
  cases hx with
  | inl hAB =>
      -- `x ∈ interior A ∪ interior B`
      cases hAB with
      | inl hxA =>
          -- Case `x ∈ interior A`
          have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          have hMono : interior (A : Set X) ⊆
              interior (A ∪ B ∪ C : Set X) := interior_mono hSub
          exact hMono hxA
      | inr hxB =>
          -- Case `x ∈ interior B`
          have hSub : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          have hMono : interior (B : Set X) ⊆
              interior (A ∪ B ∪ C : Set X) := interior_mono hSub
          exact hMono hxB
  | inr hxC =>
      -- Case `x ∈ interior C`
      have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      have hMono : interior (C : Set X) ⊆
          interior (A ∪ B ∪ C : Set X) := interior_mono hSub
      exact hMono hxC