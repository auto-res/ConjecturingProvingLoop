

theorem Topology.interiorClosureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact hSub hB