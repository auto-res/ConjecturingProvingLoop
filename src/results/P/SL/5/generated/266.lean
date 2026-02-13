

theorem closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
  classical
  ext x
  constructor
  · intro hxCl
    -- We show `x ∉ interior A`
    have hnot : x ∉ interior (A : Set X) := by
      intro hxInt
      -- Choose an open neighbourhood of `x` contained in `A`.
      rcases mem_interior.1 hxInt with ⟨U, hUsubA, hUopen, hxU⟩
      -- Since `x ∈ closure (Aᶜ)`, the neighbourhood `U` meets `Aᶜ`.
      have hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
        (mem_closure_iff).1 hxCl U hUopen hxU
      rcases hNon with ⟨y, ⟨hyU, hyCompl⟩⟩
      have hyA : y ∈ (A : Set X) := hUsubA hyU
      exact hyCompl hyA
    -- Membership in the complement is definitionally `¬`.
    exact hnot
  · intro hxNotInt
    -- `hxNotInt` is a proof that `x ∉ interior A`
    have hxCl : x ∈ closure ((A : Set X)ᶜ) := by
      -- Use the neighbourhood characterisation of the closure.
      refine (mem_closure_iff).2 ?_
      intro U hUopen hxU
      -- We must show `U ∩ Aᶜ` is non‐empty.
      by_cases hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty
      · exact hNon
      · -- If not, then `U ⊆ A`, contradicting `hxNotInt`.
        have hSub : (U : Set X) ⊆ A := by
          intro y hyU
          by_contra hyNotA
          have hyCompl : y ∈ ((A : Set X)ᶜ) := hyNotA
          have : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
            ⟨y, ⟨hyU, hyCompl⟩⟩
          exact (hNon this).elim
        have hxInt : x ∈ interior (A : Set X) :=
          mem_interior.2 ⟨U, hSub, hUopen, hxU⟩
        exact (hxNotInt hxInt).elim
    exact hxCl