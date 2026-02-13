

theorem Topology.frontier_eq_compl_interior_union_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (interior A ∪ interior (Aᶜ))ᶜ := by
  ext x
  constructor
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∉ interior A`
    have hNotIntA : x ∉ interior A := hx.2
    -- Show that `x ∉ interior (Aᶜ)`
    have hNotIntAc : x ∉ interior (Aᶜ) := by
      intro hxIntAc
      -- `interior (Aᶜ)` is open and contains `x`
      -- but it is disjoint from `A`, contradicting `x ∈ closure A`.
      have hNon :
          ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
        (mem_closure_iff).1 hx.1 (interior (Aᶜ)) isOpen_interior hxIntAc
      rcases hNon with ⟨y, ⟨hyIntAc, hyA⟩⟩
      have : (y : X) ∈ Aᶜ := interior_subset hyIntAc
      exact this hyA
    -- Hence `x` lies in the complement of the union of the interiors.
    have : x ∉ interior A ∪ interior (Aᶜ) := by
      intro h
      cases h with
      | inl hIntA  => exact hNotIntA hIntA
      | inr hIntAc => exact hNotIntAc hIntAc
    simpa [Set.mem_compl] using this
  · intro hxComp
    -- `hxComp` says `x` is not in `interior A` nor in `interior (Aᶜ)`
    have hNotUnion : x ∉ interior A ∪ interior (Aᶜ) := by
      simpa [Set.mem_compl] using hxComp
    have hNotIntA : x ∉ interior A := by
      intro hIntA
      exact hNotUnion (Or.inl hIntA)
    have hNotIntAc : x ∉ interior (Aᶜ) := by
      intro hIntAc
      exact hNotUnion (Or.inr hIntAc)
    -- Show `x ∈ closure A`
    have hClos : x ∈ closure A := by
      by_contra hNotClos
      have hxOpen : x ∈ (closure A)ᶜ := hNotClos
      have hOpenCompl : IsOpen ((closure A)ᶜ) :=
        (isClosed_closure (s := A)).isOpen_compl
      -- `(closure A)ᶜ` is an open neighbourhood of `x` contained in `Aᶜ`
      have hSub : ((closure A)ᶜ : Set X) ⊆ Aᶜ := by
        intro y hy
        by_cases hyA : y ∈ A
        · have : y ∈ closure A := subset_closure hyA
          exact (hy this).elim
        · exact hyA
      have hxIntAc : x ∈ interior (Aᶜ) :=
        (interior_maximal hSub hOpenCompl) hxOpen
      exact hNotIntAc hxIntAc
    exact And.intro hClos hNotIntA