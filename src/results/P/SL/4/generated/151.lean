

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (Aᶜ) = (closure A)ᶜ := by
  simpa using interior_compl (s := A)