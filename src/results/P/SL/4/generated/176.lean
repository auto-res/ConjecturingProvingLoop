

theorem compl_interior_compl_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    (interior (Aᶜ))ᶜ = closure A := by
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [compl_compl] using congrArg Set.compl h