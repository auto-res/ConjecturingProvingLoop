

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ (Aᶜ) = (∅ : Set X) := by
  -- First, observe that `interior A` is contained in `A`.
  have h_subset : interior A ⊆ (A : Set X) := interior_subset
  -- Establish the two inclusions needed for set equality.
  apply Set.Subset.antisymm
  · -- `interior A ∩ Aᶜ ⊆ ∅`
    intro x hx
    -- `x` lies in both `interior A` and `Aᶜ`.
    have hA : x ∈ A := h_subset hx.1
    have hAc : x ∈ Aᶜ := hx.2
    -- Contradiction.
    exact (hAc hA).elim
  · -- `∅ ⊆ interior A ∩ Aᶜ`
    exact Set.empty_subset _