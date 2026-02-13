

theorem Topology.union_interior_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A` is contained in `interior (A ∪ B)` because `A ⊆ A ∪ B`.
      have h : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hA
  | inr hB =>
      -- `interior B` is contained in `interior (A ∪ B)` because `B ⊆ A ∪ B`.
      have h : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h hB