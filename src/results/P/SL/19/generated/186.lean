

theorem Topology.frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨_, hxNotInt⟩
  -- We prove that `x ∈ closure (Aᶜ)` using the neighbourhood characterization
  have : x ∈ closure (Aᶜ) := by
    refine (mem_closure_iff).2 ?_
    intro U hU hxU
    by_cases hNon : ((U ∩ (Aᶜ)) : Set X).Nonempty
    · exact hNon
    · -- If the intersection is empty, then `U ⊆ A`
      have hSub : (U : Set X) ⊆ A := by
        intro y hy
        by_contra hAy
        have : (y : X) ∈ (U ∩ Aᶜ) := ⟨hy, hAy⟩
        exact hNon ⟨y, this⟩
      -- Hence `x ∈ interior A`, contradicting `hxNotInt`
      have hxInt : x ∈ interior A :=
        (interior_maximal hSub hU) hxU
      exact (hxNotInt hxInt).elim
  exact this