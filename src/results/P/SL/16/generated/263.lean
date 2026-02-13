

theorem Topology.interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior A ∪ closure A : Set X) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- From `x ∈ interior A`, we get `x ∈ A`, hence `x ∈ closure A`.
        have : (x : X) ∈ A := interior_subset hxInt
        exact subset_closure this
    | inr hxCl =>
        exact hxCl
  · intro hxCl
    exact Or.inr hxCl