

theorem Topology.interiorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_right
      exact hSub hxB