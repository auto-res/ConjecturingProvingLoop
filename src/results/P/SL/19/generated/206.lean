

theorem Topology.closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- Derive a contradiction from the assumption that `x` belongs to
    -- both `closure A` and `interior (Aᶜ)`.
    rcases hx with ⟨hxClos, hxIntCompl⟩
    -- Using the characterization of the closure via neighborhood
    -- intersections with open sets.
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClos _ isOpen_interior hxIntCompl
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    -- But `interior (Aᶜ)` is contained in `Aᶜ`, contradicting `y ∈ A`.
    have : (y : X) ∈ Aᶜ :=
      (interior_subset : interior (Aᶜ) ⊆ Aᶜ) hyIntCompl
    exact (this hyA).elim
  · intro x hx
    -- The right-hand side is the empty set.
    cases hx