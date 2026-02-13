

theorem Topology.closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClosCompl, hxIntA⟩
    -- `interior A` is an open neighbourhood of `x` contained in `A`.
    have hNon :
        ((interior A : Set X) ∩ Aᶜ).Nonempty :=
      (mem_closure_iff).1 hxClosCompl (interior A) isOpen_interior hxIntA
    rcases hNon with ⟨y, ⟨hyIntA, hyCompl⟩⟩
    -- The point `y` lies both in `A` and `Aᶜ`, a contradiction.
    have : (y : X) ∈ A := interior_subset hyIntA
    exact (hyCompl this).elim
  · intro x hx
    cases hx