

theorem Topology.closure_compl_eq_compl_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
  simpa using closure_compl (A := A)