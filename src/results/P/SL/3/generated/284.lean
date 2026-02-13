

theorem interior_complement_eq_empty_iff_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((Aᶜ) : Set X) = (∅ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  -- A handy rewriting of `interior (Aᶜ)`.
  have hEq : interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ :=
    interior_complement_eq_complement_closure (A := A)
  constructor
  · intro hIntEmpty
    -- Convert the assumption using `hEq`.
    have hComplEmpty : (closure (A : Set X))ᶜ = (∅ : Set X) := by
      simpa [hEq] using hIntEmpty
    -- Show that `closure A = univ`.
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    -- If `x ∉ closure A`, we get a contradiction with `hComplEmpty`.
    by_cases hx : (x : X) ∈ closure (A : Set X)
    · exact hx
    ·
      have : (x : X) ∈ (closure (A : Set X))ᶜ := hx
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hComplEmpty] using this
      exact this.elim
  · intro hDense
    -- Rewrite via `hEq` and `hDense`.
    have : interior ((Aᶜ) : Set X) = (Set.univ : Set X)ᶜ := by
      simpa [hDense] using hEq
    simpa [Set.compl_univ] using this