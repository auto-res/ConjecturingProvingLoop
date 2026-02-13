

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- First, `frontier A` is closed, hence its closure is itself.
  have h₁ : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- Next, express `frontier A` as the intersection of the two closures.
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    Topology.frontier_eq_closure_inter_closure_compl (A := A)
  -- Combine the two equalities.
  simpa [h₂] using h₁