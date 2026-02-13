

theorem Topology.dense_implies_emptyInterior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (A : Set X)) :
    interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- First, show that `interior (Aᶜ)` is contained in `∅`.
  have h_subset : interior ((A : Set X)ᶜ) ⊆ (∅ : Set X) := by
    intro x hx_int
    -- `x` lies in the closure of `A` because `A` is dense.
    have hx_closure : (x : X) ∈ closure (A : Set X) := by
      have h_cl_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
      simpa [h_cl_eq] using (by simp : (x : X) ∈ (Set.univ : Set X))
    -- Apply the characterization of closure to the open set `interior (Aᶜ)`.
    have h_nonempty :=
      (mem_closure_iff).1 hx_closure
        (interior ((A : Set X)ᶜ)) isOpen_interior hx_int
    -- Derive a contradiction: the intersection is empty.
    rcases h_nonempty with ⟨y, ⟨hy_int_comp, hy_inA⟩⟩
    have hy_notA : (y : X) ∉ A := by
      -- Points in `interior (Aᶜ)` lie in `Aᶜ`.
      have : (y : X) ∈ ((A : Set X)ᶜ) :=
        (interior_subset : interior ((A : Set X)ᶜ) ⊆ (A : Set X)ᶜ) hy_int_comp
      simpa using this
    exact False.elim (hy_notA hy_inA)
  -- Conclude that the two sets are equal.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)