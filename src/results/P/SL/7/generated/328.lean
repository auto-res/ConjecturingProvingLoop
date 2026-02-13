

theorem Topology.closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
        apply closure_mono
        exact Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
        apply closure_mono
        exact Set.subset_union_right
      exact hSub hxB