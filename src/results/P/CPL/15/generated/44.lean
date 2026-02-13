

theorem P2_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P2 (A ∪ interior A) := by
  -- Since `interior A ⊆ A`, the union is just `A`.
  have hEq : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA   => exact hA
      | inr hInt => exact interior_subset hInt
    · intro hx
      exact Or.inl hx
  simpa [hEq] using h