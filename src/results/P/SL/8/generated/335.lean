

theorem interior_closure_compl_eq_compl_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [closure_compl_eq_compl_interior (α := X) (s := A)]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (interior_compl_eq_compl_closure (X := X) (A := interior A))