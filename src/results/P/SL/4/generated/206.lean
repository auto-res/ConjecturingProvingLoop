

theorem interior_union_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure (interior A) = closure (interior A) := by
  -- We first note that `interior A` is contained in `closure (interior A)`.
  have h_sub : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Now we establish the desired set equality.
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hx_int => exact h_sub hx_int
    | inr hx_cl  => exact hx_cl
  · intro x hx
    exact Or.inr hx