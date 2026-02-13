

theorem closure_diff_interior_compl_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  -- Rewrite each difference using the `frontier` of the corresponding set.
  have h₁ :
      closure A \ interior A = frontier (A : Set X) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := A)).symm
  have h₂ :
      closure (Aᶜ) \ interior (Aᶜ) = frontier (Aᶜ) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ)).symm
  -- The frontier is invariant under taking complements.
  have h_front : frontier (Aᶜ) = frontier (A : Set X) :=
    frontier_compl_eq_frontier (X := X) (A := A)
  -- Chain the equalities to reach the goal.
  calc
    closure A \ interior A
        = frontier (A : Set X) := h₁
    _   = frontier (Aᶜ) := by
          simpa using h_front.symm
    _   = closure (Aᶜ) \ interior (Aᶜ) := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ))