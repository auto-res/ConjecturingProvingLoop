

theorem Topology.frontier_eq_closure_compl_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : closure A = (Set.univ : Set X)) :
    frontier A = closure (Aᶜ) := by
  calc
    frontier A = closure A ∩ closure (Aᶜ) := by
      simpa using
        (Topology.closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
    _ = (Set.univ : Set X) ∩ closure (Aᶜ) := by
      simpa [hDense]
    _ = closure (Aᶜ) := by
      simp