

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- `frontier A` is closed, so its closure is itself
  have h₁ : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- The frontier can be expressed as the intersection of the two closures
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    (Topology.closure_inter_closure_compl_eq_frontier (A := A)).symm
  -- Combine the two equalities
  simpa [h₁] using h₂