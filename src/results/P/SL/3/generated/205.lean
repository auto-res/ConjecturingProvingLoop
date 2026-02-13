

theorem closure_compl_eq_complement_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
  -- First inclusion: `closure (Aᶜ) ⊆ (interior A)ᶜ`.
  have h₁ : closure ((Aᶜ) : Set X) ⊆ (interior (A : Set X))ᶜ := by
    -- Since `Aᶜ ⊆ (interior A)ᶜ` and the right–hand side is closed,
    -- the claim follows from `closure_minimal`.
    have h_subset : ((Aᶜ) : Set X) ⊆ (interior (A : Set X))ᶜ := by
      intro x hxAcomp
      intro hxInt
      have hxA : (x : X) ∈ (A : Set X) := interior_subset hxInt
      exact hxAcomp hxA
    have h_closed : IsClosed ((interior (A : Set X))ᶜ) :=
      (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
    exact closure_minimal h_subset h_closed
  -- Second inclusion: `(interior A)ᶜ ⊆ closure (Aᶜ)`.
  have h₂ : (interior (A : Set X))ᶜ ⊆ closure ((Aᶜ) : Set X) := by
    intro x hxNotInt
    by_contra hxNotCl
    -- The open neighbourhood `U := (closure (Aᶜ))ᶜ` contains `x`.
    have hxU : (x : X) ∈ ((closure ((Aᶜ) : Set X))ᶜ) := hxNotCl
    have hU_open : IsOpen ((closure ((Aᶜ) : Set X))ᶜ) :=
      (isClosed_closure : IsClosed (closure ((Aᶜ) : Set X))).isOpen_compl
    -- Show that `U ⊆ A`.
    have hU_subset : ((closure ((Aᶜ) : Set X))ᶜ : Set X) ⊆ (A : Set X) := by
      intro y hy
      by_cases hYA : (y : X) ∈ (A : Set X)
      · exact hYA
      · -- Then `y ∈ Aᶜ`, hence `y ∈ closure (Aᶜ)`, contradicting `hy`.
        have hyComp : (y : X) ∈ ((Aᶜ) : Set X) := by
          simpa using hYA
        have hyCl : (y : X) ∈ closure ((Aᶜ) : Set X) := subset_closure hyComp
        have : (y : X) ∈ ((closure ((Aᶜ) : Set X))ᶜ) := hy
        exact (this hyCl).elim
    -- The point `x` is in the interior of `A`, contradicting `hxNotInt`.
    have hxIntA : (x : X) ∈ interior (A : Set X) := by
      have hxIntU :
          (x : X) ∈ interior ((closure ((Aᶜ) : Set X))ᶜ : Set X) := by
        simpa [hU_open.interior_eq] using hxU
      have hIntSubset :
          interior ((closure ((Aᶜ) : Set X))ᶜ : Set X) ⊆ interior (A : Set X) :=
        interior_mono hU_subset
      exact hIntSubset hxIntU
    exact hxNotInt hxIntA
  -- Combine the two inclusions for the desired equality.
  exact Set.Subset.antisymm h₁ h₂