

theorem Topology.closureInterior_union_closureCompl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hxc : x ∈ closure (Aᶜ)
    · exact Or.inr hxc
    · -- Since `x ∉ closure (Aᶜ)`, the open set `U = (closure (Aᶜ))ᶜ`
      -- contains `x` and is contained in `A`.
      have hxU : x ∈ ((closure (Aᶜ) : Set X)ᶜ) := by
        simpa using hxc
      have hU_open : IsOpen ((closure (Aᶜ) : Set X)ᶜ) :=
        (isClosed_closure : IsClosed (closure (Aᶜ))).isOpen_compl
      have hU_subsetA : ((closure (Aᶜ) : Set X)ᶜ) ⊆ A := by
        intro y hy
        by_contra hAy
        have hyAc : y ∈ (Aᶜ : Set X) := hAy
        have : y ∈ closure (Aᶜ) := subset_closure hyAc
        exact hy this
      -- Hence `x ∈ interior A`.
      have hx_intA : x ∈ interior A := by
        have h_subset : ((closure (Aᶜ) : Set X)ᶜ) ⊆ interior A :=
          interior_maximal hU_subsetA hU_open
        exact h_subset hxU
      -- Therefore `x ∈ closure (interior A)`.
      have hx_closureInt : x ∈ closure (interior A) := subset_closure hx_intA
      exact Or.inl hx_closureInt