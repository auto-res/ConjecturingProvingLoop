

theorem closure_unionInterior_subset_closure_interiorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  -- First, show that `interior A ∪ interior B ⊆ interior (A ∪ B)`.
  have h_sub : (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro y hy
    cases hy with
    | inl hA =>
        -- Points of `interior A` are certainly in `interior (A ∪ B)`.
        have : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact this hA
    | inr hB =>
        -- Symmetric argument for `interior B`.
        have : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact this hB
  -- Taking closures preserves inclusions.
  exact fun x hx => (closure_mono h_sub) hx