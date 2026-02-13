

theorem interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((A : Set X)ᶜ)) = (closure (interior A))ᶜ := by
  -- First, rewrite the inner `closure` using the complement–interior correspondence.
  have h₁ : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute this equality and apply the analogous rule for `interior`.
  calc
    interior (closure ((A : Set X)ᶜ)) =
        interior ((interior (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (closure (interior (A : Set X)))ᶜ := by
          simpa using
            interior_compl_eq_compl_closure
              (X := X) (A := interior (A : Set X))