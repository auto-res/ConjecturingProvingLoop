

theorem Topology.dense_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ interior (Aᶜ) = (∅ : Set X) := by
  classical
  constructor
  · intro hDense
    exact interior_compl_eq_empty_of_dense (A := A) hDense
  · intro hIntEmpty
    -- Show `closure A = univ`, then invoke an existing equivalence.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      by_cases hx : x ∈ closure A
      · exact hx
      ·
        -- `x` belongs to the open set `(closure A)ᶜ`
        have hx_mem : x ∈ (closure A)ᶜ := by
          simpa [Set.mem_compl] using hx
        have hOpen : IsOpen ((closure A)ᶜ) :=
          isClosed_closure.isOpen_compl
        -- `(closure A)ᶜ` is an open subset of `Aᶜ`
        have h_subset : (closure A)ᶜ ⊆ Aᶜ := by
          intro y hy
          by_cases hAy : y ∈ A
          · have : y ∈ closure A := subset_closure hAy
            exact False.elim (hy this)
          · simpa [Set.mem_compl] using hAy
        -- Therefore it is contained in `interior (Aᶜ)`
        have hx_int : x ∈ interior (Aᶜ) :=
          (interior_maximal h_subset hOpen) hx_mem
        -- Contradicts the assumption `interior (Aᶜ) = ∅`
        simpa [hIntEmpty] using hx_int
    have h_closure_eq :
        closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_univ_subset
    exact
      ((Topology.dense_iff_closure_eq_univ (A := A)).2 h_closure_eq)