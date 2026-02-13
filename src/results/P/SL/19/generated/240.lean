

theorem Topology.interior_compl_inter_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) ∩ frontier A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntCompl, hxFront⟩
    have hxClosA : x ∈ closure A := hxFront.1
    -- The open neighbourhood `interior (Aᶜ)` of `x` is disjoint from `A`,
    -- contradicting `x ∈ closure A`.
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClosA (interior (Aᶜ)) isOpen_interior hxIntCompl
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    have : (y : X) ∈ Aᶜ := interior_subset hyIntCompl
    exact (this hyA).elim
  · exact Set.empty_subset _