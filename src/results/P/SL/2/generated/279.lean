

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier ((Aᶜ) : Set X) = frontier (A : Set X) := by
  calc
    frontier ((Aᶜ) : Set X)
        = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa [Set.compl_compl, Set.inter_comm] using
            (Topology.frontier_eq_closure_inter_closure_compl
                (A := (Aᶜ : Set X)))
    _ = frontier (A : Set X) := by
          simpa using
            (Topology.frontier_eq_closure_inter_closure_compl
                (A := A)).symm