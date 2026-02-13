

theorem frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier A = closure A \ interior A := by
  -- Begin with the characterization of the frontier as an intersection
  have h₁ : closure A ∩ closure (Aᶜ) = frontier A := by
    simpa using
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A))
  -- Express the set difference as an intersection with a complement
  have h₂ : closure A \ interior A = closure A ∩ (interior A)ᶜ := rfl
  -- Relate `closure (Aᶜ)` to the complement of `interior A`
  have h₃ : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  -- Rewrite the frontier using `h₃`
  have h₄ : frontier A = closure A ∩ (interior A)ᶜ := by
    simpa [h₃] using h₁.symm
  -- Conclude by substituting the two intermediate identities
  simpa [h₂] using h₄