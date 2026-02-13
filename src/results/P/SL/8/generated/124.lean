

theorem interior_closure_union_subset_interior_closureUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`
      -- Since `closure A ⊆ closure (A ∪ B)`, taking interiors yields the desired inclusion.
      have h_closure : closure A ⊆ closure (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono h_sub
      have h_interior : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure
      exact h_interior hxA
  | inr hxB =>
      -- Symmetric argument for `x ∈ interior (closure B)`
      have h_closure : closure B ⊆ closure (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono h_sub
      have h_interior : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure
      exact h_interior hxB