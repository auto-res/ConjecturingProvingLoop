

theorem Topology.frontier_eq_empty_iff_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  classical
  constructor
  · intro h_frontier
    -- From `frontier A = ∅` we deduce `closure A ⊆ interior A`.
    have h_subset : closure A ⊆ interior A := by
      intro x hx_cl
      by_contra hx_int
      have : x ∈ frontier (A : Set X) := ⟨hx_cl, hx_int⟩
      simpa [h_frontier] using this
    -- Hence `interior A ⊆ A ⊆ closure A ⊆ interior A`,
    -- so all three sets coincide.
    have h_int_eq : interior A = (A : Set X) := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        have hx_cl : x ∈ closure A := subset_closure hxA
        exact h_subset hx_cl
    have h_cl_eq : closure A = (A : Set X) := by
      apply subset_antisymm
      · intro x hx_cl
        exact (interior_subset : interior A ⊆ A) (h_subset hx_cl)
      · exact subset_closure
    -- Use these equalities to obtain openness and closedness.
    have h_open : IsOpen A := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have h_closed : IsClosed A := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact ⟨h_closed, h_open⟩
  · rintro ⟨h_closed, h_open⟩
    exact Topology.frontier_eq_empty_of_isClopen (A := A) h_closed h_open