

theorem Topology.boundary_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    closure A \ interior A ⊆ Aᶜ := by
  intro x hx
  -- `hx` provides `x ∈ closure A` and `x ∉ interior A`.
  -- Since `A` is open, `interior A = A`.
  have h_notA : x ∉ A := by
    have h_not_int : x ∉ interior A := hx.2
    simpa [hOpen.interior_eq] using h_not_int
  -- Membership in the complement is exactly the negation of membership in `A`.
  exact h_notA