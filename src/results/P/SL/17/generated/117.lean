

theorem Topology.union_interior_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact hsubset hA
  | inr hB =>
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact hsubset hB