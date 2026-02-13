

theorem Topology.P1_of_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) → Topology.P1 A := by
  intro hFrontier
  intro x hxA
  by_cases hx_int : x ∈ interior A
  · exact subset_closure hx_int
  ·
    have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
    have hx_frontier : x ∈ frontier (A : Set X) := by
      exact And.intro hx_closure hx_int
    exact hFrontier hx_frontier