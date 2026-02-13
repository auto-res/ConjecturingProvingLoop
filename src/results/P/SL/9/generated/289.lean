

theorem Topology.closure_union_interior_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A ∪ interior A) = closure A := by
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA      => exact hxA
      | inr hxIntA   => exact interior_subset hxIntA
    · intro hxA
      exact Or.inl hxA
  simpa [h_union]