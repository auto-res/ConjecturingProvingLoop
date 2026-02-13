

theorem Topology.frontier_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (Aᶜ) := by
  intro x hx
  have h : x ∈ closure A ∩ closure (Aᶜ) := by
    simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)] using hx
  exact h.2