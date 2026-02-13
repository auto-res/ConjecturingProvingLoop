

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
  simpa [compl_compl] using
    (Topology.interior_eq_compl_closure_compl (X := X) (A := ((A : Set X)ᶜ)))