

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) ⊆
      closure (interior (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ closure (interior A)`.
      have hSub : closure (interior (A : Set X)) ⊆
          closure (interior (A ∪ B : Set X)) := by
        -- `interior A` is contained in `interior (A ∪ B)`.
        have hIntSub : interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        -- Taking closures preserves inclusions.
        exact closure_mono hIntSub
      exact hSub hxA
  | inr hxB =>
      -- Handle the case `x ∈ closure (interior B)`.
      have hSub : closure (interior (B : Set X)) ⊆
          closure (interior (A ∪ B : Set X)) := by
        -- `interior B` is contained in `interior (A ∪ B)`.
        have hIntSub : interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        -- Taking closures preserves inclusions.
        exact closure_mono hIntSub
      exact hSub hxB