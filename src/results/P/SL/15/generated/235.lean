

theorem closure_union_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `closure A` is contained in the closure of the union.
      have h_subset : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
        exact closure_mono this
      exact h_subset hA
  | inr hB =>
      -- `closure B` is contained in the closure of the union.
      have h_subset : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
        exact closure_mono this
      exact h_subset hB