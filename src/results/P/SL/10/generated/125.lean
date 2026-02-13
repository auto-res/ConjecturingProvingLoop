

theorem Topology.interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior A`; use monotonicity `interior_mono`.
      have h_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_subset hxA
  | inr hxB =>
      -- `x ∈ interior B`; similar argument.
      have h_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact h_subset hxB