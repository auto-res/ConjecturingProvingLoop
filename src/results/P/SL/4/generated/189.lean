

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` using the standard complement formula.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Substitute the rewrite into the goal and apply the corresponding
  -- formula for the closure of a complement.
  calc
    closure (interior (Aᶜ)) = closure ((closure A)ᶜ) := by
      simpa [h₁]
    _ = (interior (closure A))ᶜ := by
      simpa using
        (closure_compl_eq_compl_interior (A := closure A))