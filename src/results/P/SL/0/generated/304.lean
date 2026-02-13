

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxCl => exact hxCl
    | inr hxInt =>
        have hxA : x ∈ (A : Set X) := interior_subset hxInt
        exact (subset_closure hxA)
  · intro hx
    exact Or.inl hx