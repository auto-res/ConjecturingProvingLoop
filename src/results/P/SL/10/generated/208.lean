

theorem Topology.closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hCl => exact hCl
    | inr hInt =>
        exact subset_closure (interior_subset hInt)
  · intro x hx
    exact Or.inl hx