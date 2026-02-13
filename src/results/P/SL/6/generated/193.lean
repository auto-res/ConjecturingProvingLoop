

theorem union_interior_closure_interior_subset_interior_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Show that `interior (closure (interior A))` is included in the target.
      have hIncl :
          closure (interior (A : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      have hIntIncl :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) :=
        interior_mono hIncl
      exact hIntIncl hxA
  | inr hxB =>
      -- Symmetric argument for the `B` component.
      have hIncl :
          closure (interior (B : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      have hIntIncl :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) :=
        interior_mono hIncl
      exact hIntIncl hxB