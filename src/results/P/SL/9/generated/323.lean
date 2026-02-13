

theorem Topology.isOpen_iff_frontier_subset_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) ↔ frontier (A : Set X) ⊆ Aᶜ := by
  classical
  constructor
  · intro hA_open
    -- For an open set, the frontier is `closure A \ A`, whence the claim.
    intro x hx_front
    have h_frontier :
        frontier (A : Set X) = closure A \ A :=
      Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA_open
    have : x ∈ closure A \ A := by
      simpa [h_frontier] using hx_front
    exact this.2
  · intro h_frontier_sub
    -- Show `A ⊆ interior A`; the reverse inclusion is automatic.
    have h_eq_int : interior (A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        by_contra hx_not_int
        -- Then `x` lies in the frontier, contradicting the assumption.
        have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
        have hx_front : x ∈ frontier (A : Set X) := ⟨hx_cl, hx_not_int⟩
        have : x ∈ (Aᶜ : Set X) := h_frontier_sub hx_front
        exact this hxA
    -- An interior equals the set itself iff the set is open.
    simpa [h_eq_int] using (isOpen_interior : IsOpen (interior A))