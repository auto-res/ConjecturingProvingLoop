

theorem interior_union_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∪ closure A) = interior (closure A) := by
  -- First, observe that `A ∪ closure A` coincides with `closure A`.
  have h_union : (A ∪ closure A : Set X) = closure A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA   => exact subset_closure hA
      | inr hClA => exact hClA
    · intro hx
      exact Or.inr hx
  -- Rewrite the goal using the equality just established.
  simpa [h_union]