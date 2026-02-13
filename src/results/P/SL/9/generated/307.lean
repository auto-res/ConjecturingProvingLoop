

theorem Topology.closure_inter_frontier_eq_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ frontier A = frontier A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨hx.1, hx⟩