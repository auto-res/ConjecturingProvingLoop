

theorem Topology.interior_union_interior_eq_self {X : Type*} [TopologicalSpace X]
    (A : Set X) : interior (A ∪ interior A) = interior A := by
  -- First, observe that `A ∪ interior A` is just `A`,
  -- since `interior A ⊆ A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA      => exact hA
      | inr hIntA   => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  -- Rewrite using this equality.
  simpa [h_union]