

theorem interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  -- First, express `closure (Aᶜ)` as the complement of `interior A`.
  have h₁ : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Take interiors of both sides and rewrite using `interior_compl`.
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [h₁]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (interior_compl (s := interior A))