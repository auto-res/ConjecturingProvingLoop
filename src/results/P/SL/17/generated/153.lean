

theorem Topology.compl_closure_interior_eq_interior_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A))ᶜ = interior (closure (Aᶜ)) := by
  simpa [closure_compl] using
    (interior_compl (A := interior A)).symm