

theorem Topology.interiorClosureCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_int_cl_compl, hx_intA⟩
  -- From `x ∈ interior (closure (Aᶜ))`, deduce `x ∈ closure (Aᶜ)`.
  have hx_cl_compl : x ∈ closure (Aᶜ) := interior_subset hx_int_cl_compl
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have h_subset : closure (Aᶜ : Set X) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  -- Hence `x ∉ interior A`, contradicting `hx_intA`.
  have hx_not_intA : x ∉ interior A := by
    have hx' : x ∈ (interior A)ᶜ := h_subset hx_cl_compl
    simpa using hx'
  exact hx_not_intA hx_intA