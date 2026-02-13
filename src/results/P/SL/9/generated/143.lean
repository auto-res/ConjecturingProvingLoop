

theorem Topology.closure_inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no point belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_cl, hx_int⟩
  -- Every neighbourhood of `x` meets `A`, since `x ∈ closure A`.
  have h_nonempty : ((interior (Aᶜ)) ∩ A).Nonempty := by
    have h_closure := (mem_closure_iff).1 hx_cl
    exact h_closure _ isOpen_interior hx_int
  -- Pick a point in the non-empty intersection and derive a contradiction.
  rcases h_nonempty with ⟨y, ⟨hy_int_compl, hyA⟩⟩
  have hy_notA : y ∈ Aᶜ := interior_subset hy_int_compl
  exact (hy_notA hyA).elim