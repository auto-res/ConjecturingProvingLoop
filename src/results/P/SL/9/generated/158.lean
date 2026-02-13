

theorem Topology.closureInteriorCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_cl, hx_intA⟩
  -- Because `x` is in the closure of `interior (Aᶜ)` and
  -- `interior A` is an open neighbourhood of `x`,
  -- these two sets must meet.
  have h_nonempty : ((interior A) ∩ interior (Aᶜ)).Nonempty := by
    have h := (mem_closure_iff).1 hx_cl
    exact h _ isOpen_interior hx_intA
  -- But a point cannot lie in both `A` and `Aᶜ`.
  rcases h_nonempty with ⟨y, ⟨hy_intA, hy_intAc⟩⟩
  have hyA  : y ∈ A   := interior_subset hy_intA
  have hyAc : y ∈ Aᶜ := interior_subset hy_intAc
  exact hyAc hyA