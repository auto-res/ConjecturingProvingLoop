

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
  simpa using interior_compl (A := A)