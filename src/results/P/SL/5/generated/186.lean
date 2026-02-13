

theorem closure_union_three_subset {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A : Set X) ∪ closure B ∪ closure C ⊆ closure (A ∪ B ∪ C) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hxA =>
          -- Case `x ∈ closure A`
          have hsubset : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          exact (closure_mono hsubset) hxA
      | inr hxB =>
          -- Case `x ∈ closure B`
          have hsubset : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          exact (closure_mono hsubset) hxB
  | inr hxC =>
      -- Case `x ∈ closure C`
      have hsubset : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact (closure_mono hsubset) hxC