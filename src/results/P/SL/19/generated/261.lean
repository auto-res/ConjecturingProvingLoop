

theorem Topology.frontier_eq_closure_compl_diff_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = closure (Aᶜ) \ interior (Aᶜ) := by
  calc
    frontier A = frontier (Aᶜ) := by
      simpa using (Topology.frontier_compl (A := A)).symm
    _ = closure (Aᶜ) \ interior (Aᶜ) := by
      simpa using
        (Topology.frontier_eq_closure_diff_interior (A := Aᶜ))