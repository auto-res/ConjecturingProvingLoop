

theorem Topology.closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = closure A \ interior A := by
  simpa using
    (Topology.closure_diff_interior_eq_closure_inter_closure_compl
        (X := X) (A := A)).symm