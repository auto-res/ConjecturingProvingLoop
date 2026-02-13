

theorem Topology.closureInterior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_right
      exact hSub hxB