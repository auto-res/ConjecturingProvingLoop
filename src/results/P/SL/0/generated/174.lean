

theorem union_interiors_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      interior (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior A`.
      have hMono : interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hMono hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior B`.
      have hMono : interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hMono hxB