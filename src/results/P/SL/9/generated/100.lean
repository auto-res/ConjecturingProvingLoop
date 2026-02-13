

theorem Topology.closure_compl_subset_compl_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ⊆ (interior A)ᶜ := by
  intro x hx_closure
  -- We must show `x ∉ interior A`.
  intro hx_intA
  -- Use the characterization of closure: every neighbourhood of `x` meets `Aᶜ`.
  have h_nonempty : ((interior A) ∩ Aᶜ).Nonempty := by
    have h_closure := (mem_closure_iff).1 hx_closure
    exact h_closure _ isOpen_interior hx_intA
  -- Derive a contradiction from the non-empty intersection.
  rcases h_nonempty with ⟨y, ⟨hy_int, hy_compl⟩⟩
  have hyA : y ∈ A := interior_subset hy_int
  exact hy_compl hyA