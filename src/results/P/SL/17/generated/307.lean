

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  -- Express both frontiers via closures and complements.
  have h₁ : frontier (Aᶜ) = closure (Aᶜ) ∩ closure A := by
    simpa [Set.compl_compl] using
      (Topology.frontier_eq_closure_inter_closure_compl (A := Aᶜ))
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) := by
    simpa using
      (Topology.frontier_eq_closure_inter_closure_compl (A := A))
  -- The right‐hand sides are equal up to commutativity of `∩`.
  simpa [h₁, h₂, Set.inter_comm]