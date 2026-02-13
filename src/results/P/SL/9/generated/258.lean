

theorem Topology.frontier_eq_inter_closure_closureCompl
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = closure A ∩ closure (Aᶜ) := by
  have h₁ := Topology.frontier_eq_closure_diff_interior (A := A)
  have h₂ := (Topology.closure_inter_closureCompl_eq_closure_diff_interior (A := A)).symm
  simpa using h₁.trans h₂