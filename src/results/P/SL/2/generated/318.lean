

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) =
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using
            (Topology.closure_frontier_eq_frontier (A := A))
    _ = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa using
            (Topology.frontier_eq_closure_inter_closure_compl (A := A))