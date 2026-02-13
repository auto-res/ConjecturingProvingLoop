

theorem closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- It suffices to show the inclusion at the level of the sets,
  -- and then use `closure_mono`.
  apply closure_mono
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior A`, which is contained in `interior (A ∪ B)`.
      have hsubset : (interior (A : Set X) : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hxB =>
      -- Symmetric argument for the case `x ∈ interior B`.
      have hsubset : (interior (B : Set X) : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB