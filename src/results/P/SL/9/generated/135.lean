

theorem Topology.closureCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ∩ interior A = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing that no point belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_closure, hx_int⟩
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have hsubset : closure (Aᶜ : Set X) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  have : x ∈ (interior A)ᶜ := hsubset hx_closure
  exact this hx_int