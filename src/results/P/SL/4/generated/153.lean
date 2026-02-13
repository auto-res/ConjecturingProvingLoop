

theorem interior_closure_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A ∪ interior A)) = interior (closure A) := by
  -- First, show that `A ∪ interior A = A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  -- Rewrite using the established equality.
  simpa [h_union]