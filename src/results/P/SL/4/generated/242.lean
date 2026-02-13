

theorem interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hInt =>
        -- `x` lies in `interior A`, hence in `A`, hence in `closure A`.
        exact
          (subset_closure (interior_subset hInt))
    | inr hCl =>
        exact hCl
  · intro x hx
    -- Any point of `closure A` is in the right component of the union.
    exact Or.inr hx