

theorem union_interior_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x` lies in `interior (closure A)`
      -- Show that this interior is contained in the desired interior.
      have hIncl : closure (A : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      have hIntIncl :
          interior (closure (A : Set X))
            ⊆ interior (closure (A ∪ B)) :=
        interior_mono hIncl
      exact hIntIncl hAx
  | inr hBx =>
      -- Analogous argument for the `B` component.
      have hIncl : closure (B : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      have hIntIncl :
          interior (closure (B : Set X))
            ⊆ interior (closure (A ∪ B)) :=
        interior_mono hIncl
      exact hIntIncl hBx