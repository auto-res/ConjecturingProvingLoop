

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_dense : Dense (A : Set X)) :
    frontier (A : Set X) = (Aᶜ : Set X) := by
  have h_frontier :
      frontier (A : Set X) = closure (A : Set X) \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA_open
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hA_dense.closure_eq
  simpa [h_closure, Set.diff_eq, Set.inter_univ, Set.univ_inter] using h_frontier