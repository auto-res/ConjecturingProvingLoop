

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  have h₁ : interior (Aᶜ) = (closure A)ᶜ := by
    simpa using
      (interior_compl_eq_compl_closure (X := X) (A := A))
  have h₂ : closure ((closure A)ᶜ) = (interior (closure A))ᶜ := by
    simpa using
      (closure_compl_eq_compl_interior (α := X) (s := closure A))
  simpa [h₁] using h₂