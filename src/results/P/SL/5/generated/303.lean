

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior ((A : Set X)ᶜ)) =
      (interior (closure (A : Set X)))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h₁ :
      interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  -- Substitute this equality and apply the corresponding rule for `closure`.
  calc
    closure (interior ((A : Set X)ᶜ)) =
        closure ((closure (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (interior (closure (A : Set X)))ᶜ := by
          simpa using
            closure_compl_eq_compl_interior
              (X := X) (A := closure (A : Set X))