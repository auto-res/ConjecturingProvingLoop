

theorem Topology.interior_closure_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`
      have hsubset_closure : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure B)`
      have hsubset_closure : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hxB