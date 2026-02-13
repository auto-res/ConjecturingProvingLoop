

theorem Topology.closureInteriorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (closure A)) ∪ closure (interior (closure B)) ⊆
      closure (interior (closure (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : closure (interior (closure A)) ⊆
          closure (interior (closure (A ∪ B))) := by
        apply closure_mono
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : closure (interior (closure B)) ⊆
          closure (interior (closure (A ∪ B))) := by
        apply closure_mono
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact hSub hB