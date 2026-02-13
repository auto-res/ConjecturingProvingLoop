

theorem compl_frontier_eq_compl_closure_union_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (frontier A)ᶜ = (closure A)ᶜ ∪ interior A := by
  -- First, rewrite the frontier as an intersection.
  have h₁ : (frontier A : Set X) = closure A ∩ (interior A)ᶜ := by
    have h := frontier_eq_closure_diff_interior (X := X) (A := A)
    simpa [Set.diff_eq] using h
  -- Take complements of both sides.
  have h₂ : (frontier A)ᶜ = (closure A ∩ (interior A)ᶜ)ᶜ := by
    simpa [h₁]
  -- Use De Morgan's laws to simplify the right-hand side.
  simpa [Set.compl_inter, Set.compl_compl] using h₂