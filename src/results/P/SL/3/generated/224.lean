

theorem interior_closure_complement_eq_complement_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((Aᶜ) : Set X)) =
      (closure (interior (A : Set X)))ᶜ := by
  have h₁ :
      closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
    simpa using
      (closure_complement_eq_complement_interior (A := A))
  have h₂ :
      interior ((interior (A : Set X))ᶜ) =
        (closure (interior (A : Set X)))ᶜ := by
    simpa using
      (interior_complement_eq_complement_closure
        (A := interior (A : Set X)))
  simpa [h₁] using h₂