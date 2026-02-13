

theorem Topology.closureInterior_inter_interiorCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We show that every point is *not* in the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_closure, hx_int_compl⟩
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  -- Since `x` lies in the closure of `interior A`, this neighbourhood
  -- meets `interior A`.
  have h_nonempty : ((interior (Aᶜ)) ∩ interior A).Nonempty := by
    have hx := (mem_closure_iff).1 hx_closure
    exact hx _ isOpen_interior hx_int_compl
  rcases h_nonempty with ⟨y, ⟨hy_int_compl, hy_intA⟩⟩
  -- Derive the contradiction `y ∈ A` and `y ∈ Aᶜ`.
  have hyA : y ∈ A := interior_subset hy_intA
  have hyA_compl : y ∈ Aᶜ := interior_subset hy_int_compl
  exact hyA_compl hyA