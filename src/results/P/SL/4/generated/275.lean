

theorem interior_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∪ interior A) = interior A := by
  -- Since `interior A ⊆ A`, the union is just `A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA    => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  simpa [h_union]