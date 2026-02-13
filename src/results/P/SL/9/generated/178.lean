

theorem Topology.boundary_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure (Aᶜ) := by
  classical
  intro x hx
  -- `x` lies in the closure of `A` but not in its interior.
  have hx_not_int : x ∉ interior (A : Set X) := hx.2
  -- We prove by contradiction that `x ∈ closure (Aᶜ)`.
  by_contra h_not
  -- The complement of `closure (Aᶜ)` is an open neighbourhood of `x`.
  set U : Set X := ((closure (Aᶜ) : Set X)ᶜ) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using (isClosed_closure : IsClosed (closure (Aᶜ))).isOpen_compl
  have hxU : x ∈ U := by
    have : x ∉ closure (Aᶜ) := by
      simpa using h_not
    simpa [hU_def] using this
  -- Show that `U ⊆ A`.  Indeed, if `y ∈ U` but `y ∉ A`, then `y ∈ Aᶜ`
  -- whence `y ∈ closure (Aᶜ)`, contradicting `y ∈ U = (closure (Aᶜ))ᶜ`.
  have hU_subset_A : U ⊆ (A : Set X) := by
    intro y hyU
    have hy_not_closure : y ∉ closure (Aᶜ) := by
      simpa [hU_def] using hyU
    by_cases hAy : y ∈ (A : Set X)
    · exact hAy
    · have hyAc : y ∈ (Aᶜ : Set X) := hAy
      have : y ∈ closure (Aᶜ) := subset_closure hyAc
      exact (hy_not_closure this).elim
  -- Hence `x` belongs to an open set `U` contained in `A`, so `x ∈ interior A`,
  -- contradicting `hx_not_int`.
  have hx_intA : x ∈ interior (A : Set X) := by
    -- `interior_maximal` supplies the required inclusion.
    have h_incl : U ⊆ interior (A : Set X) :=
      interior_maximal hU_subset_A hU_open
    exact h_incl hxU
  exact hx_not_int hx_intA