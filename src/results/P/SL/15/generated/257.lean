

theorem dense_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) → Dense A := by
  intro hIntEq
  -- First, show that `closure A = univ`.
  have hClosureEq : closure A = (Set.univ : Set X) := by
    -- `interior (closure A)` is contained in `closure A`.
    have hIntSub : interior (closure A) ⊆ closure A := interior_subset
    -- Hence `univ ⊆ closure A`.
    have hUnivSub : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have : x ∈ interior (closure A) := by
        simpa [hIntEq]
      exact hIntSub this
    -- Combine the trivial inclusion `closure A ⊆ univ` with the one above.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · exact hUnivSub
  -- Translate the closure equality into density.
  exact
    ((dense_iff_closure_eq (s := A)).2 hClosureEq)