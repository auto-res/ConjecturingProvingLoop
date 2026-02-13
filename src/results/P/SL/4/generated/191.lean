

theorem interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A = (closure (Aᶜ))ᶜ := by
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  calc
    interior A = ((interior A)ᶜ)ᶜ := by
      simp
    _ = (closure (Aᶜ))ᶜ := by
      simpa [h]