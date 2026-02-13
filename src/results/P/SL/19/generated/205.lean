

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  calc
    frontier (Aᶜ)
        = closure (Aᶜ) ∩ closure ((Aᶜ)ᶜ) := by
          simpa using
            (Topology.closure_inter_closure_compl_eq_frontier
              (X := X) (A := Aᶜ)).symm
    _ = closure A ∩ closure (Aᶜ) := by
          simp [compl_compl, Set.inter_comm, Set.inter_left_comm]
    _ = frontier A := by
          simpa using
            (Topology.closure_inter_closure_compl_eq_frontier
              (X := X) (A := A)).symm