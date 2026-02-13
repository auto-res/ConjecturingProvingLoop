

theorem Topology.interior_compl_eq_empty_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro hDense
  apply Set.Subset.antisymm
  · intro x hxInt
    -- `interior (Aᶜ)` is an open neighbourhood of `x`
    have hOpen : IsOpen (interior (Aᶜ)) := isOpen_interior
    -- Since `closure A = univ`, we have `x ∈ closure A`
    have hxClos : x ∈ closure A := by
      simpa [hDense] using (Set.mem_univ x)
    -- Therefore this open neighbourhood meets `A`
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClos (interior (Aᶜ)) hOpen hxInt
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradiction
    have : (y : X) ∈ Aᶜ :=
      (interior_subset : interior (Aᶜ) ⊆ Aᶜ) hyIntCompl
    exact (this hyA).elim
  ·
    intro x hx
    cases hx