

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxA
  | inr hxB =>
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_right
        exact this
      exact hsubset hxB