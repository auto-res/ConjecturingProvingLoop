

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hxCl => exact hxCl
    | inr hxInt =>
        have : (x : X) ∈ (A : Set X) := interior_subset hxInt
        exact subset_closure this
  · intro x hx
    exact Or.inl hx