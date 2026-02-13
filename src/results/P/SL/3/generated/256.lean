

theorem closure_complement_eq_complement_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
  simpa using closure_compl_eq_complement_interior (A := A)