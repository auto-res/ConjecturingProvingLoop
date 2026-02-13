

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    closure (A : Set X) = Set.univ := by
  -- We establish the two inclusions separately.
  apply le_antisymm
  · -- `closure A ⊆ univ` is trivial.
    intro x _
    trivial
  · -- Show `univ ⊆ closure A`.
    intro x _
    -- Using the hypothesis, `x ∈ interior A`.
    have hxInt : x ∈ interior (A : Set X) := by
      simpa [h]
    -- `interior A ⊆ A`.
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    -- `A ⊆ closure A`.
    exact subset_closure hxA