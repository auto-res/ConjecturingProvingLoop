

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hxA
  | inr hxB =>
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hxB