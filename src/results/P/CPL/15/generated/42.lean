

theorem P2_dense_interior_union {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = Set.univ) : P2 (A ∪ interior A) := by
  -- `interior A` is contained in `A`, hence their union is just `A`.
  have h_union_eq : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA      => exact hxA
      | inr hxIntA   => exact interior_subset hxIntA
    · intro hxA
      exact Or.inl hxA
  -- From the density hypothesis we already have `P2 A`.
  have hP2 : P2 A := P2_of_dense_interior (A := A) hd
  -- Rewriting with the previous equality yields the desired statement.
  simpa [h_union_eq] using hP2