

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- First, lift `x ∈ interior A` to `x ∈ interior (A ∪ B)`.
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact (interior_mono hSub) hAx
      -- Then, use monotonicity of `interior` with `A ∪ B ⊆ closure (A ∪ B)`.
      have hIncl :
          interior (A ∪ B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (subset_closure : (A ∪ B : Set X) ⊆ closure (A ∪ B))
      exact hIncl hx_int_union
  | inr hBx =>
      -- Symmetric argument for the `B` component.
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact (interior_mono hSub) hBx
      have hIncl :
          interior (A ∪ B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (subset_closure : (A ∪ B : Set X) ⊆ closure (A ∪ B))
      exact hIncl hx_int_union