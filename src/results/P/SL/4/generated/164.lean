

theorem closure_interior_union_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A ∪ interior A)) = closure (interior A) := by
  -- Since `interior A ⊆ A`, we have `A ∪ interior A = A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  simpa [h_union]