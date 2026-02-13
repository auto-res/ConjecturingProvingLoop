

theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ frontier (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact
      Topology.P1_implies_frontier_subset_closure_interior (A := A) hP1
  · intro hFront
    exact
      Topology.P1_of_frontier_subset_closure_interior (A := A) hFront