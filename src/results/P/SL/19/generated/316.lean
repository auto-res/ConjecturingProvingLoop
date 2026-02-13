

theorem Topology.closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hClos => exact hClos
    | inr hInt =>
        have : (x : X) ∈ A := interior_subset hInt
        exact subset_closure this
  · intro x hx
    exact Or.inl hx