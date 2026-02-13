

theorem Topology.interiors_union_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior A ⊆ interior (A ∪ B) :=
        interior_mono Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : interior B ⊆ interior (A ∪ B) :=
        interior_mono Set.subset_union_right
      exact hSub hB