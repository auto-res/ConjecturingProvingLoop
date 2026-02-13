

theorem interior_union {α : Type*} [TopologicalSpace α] {A B : Set α} :
    (interior (A : Set α)) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A ⊆ interior (A ∪ B)` because `A ⊆ A ∪ B`.
      have h_sub : (interior (A : Set α)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set α) ⊆ A ∪ B)
      exact h_sub hA
  | inr hB =>
      -- Symmetric argument for `interior B`.
      have h_sub : (interior (B : Set α)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set α) ⊆ A ∪ B)
      exact h_sub hB