

theorem Topology.closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A ⊆ A ∪ B`, so the monotonicity of `closure` yields the result.
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_subset hA
  | inr hB =>
      -- Symmetric argument for the second summand.
      have h_subset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact h_subset hB