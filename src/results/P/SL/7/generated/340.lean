

theorem Topology.closure_union_three_subset {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) ⊆
      closure (A ∪ B ∪ C : Set X) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          -- Case `x ∈ closure A`
          have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          exact (closure_mono hSub) hA
      | inr hB =>
          -- Case `x ∈ closure B`
          have hSub : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          exact (closure_mono hSub) hB
  | inr hC =>
      -- Case `x ∈ closure C`
      have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact (closure_mono hSub) hC