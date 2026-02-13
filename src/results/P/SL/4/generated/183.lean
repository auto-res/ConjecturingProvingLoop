

theorem interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hIntA, hIntAc⟩
    -- From the two interior memberships, derive membership in `A ∩ Aᶜ`,
    -- which is empty.
    have hAAc : x ∈ (A ∩ Aᶜ) := by
      exact And.intro (interior_subset hIntA) (interior_subset hIntAc)
    simpa [Set.inter_compl_self] using hAAc
  · exact Set.empty_subset _