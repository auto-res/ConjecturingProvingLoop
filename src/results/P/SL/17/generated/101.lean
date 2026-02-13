

theorem Topology.closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hclosure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hxA
  | inr hxB =>
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hclosure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hxB