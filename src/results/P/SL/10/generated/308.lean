

theorem Topology.interior_eq_closure_iff_open_and_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A = closure A ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h_eq
    -- First show `A = interior A`.
    have h_subset_int : (A : Set X) ⊆ interior A := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h_eq] using this
    have h_int_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset_int
    -- Next show `A = closure A`.
    have h_cl_eq : closure A = A := by
      have : (closure A : Set X) = interior A := by
        simpa [h_eq]
      simpa [this, h_int_eq] using rfl
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen A := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have h_closed : IsClosed A := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    -- For an open and closed set, `interior` and `closure` coincide with the set itself.
    simpa [h_open.interior_eq, h_closed.closure_eq]