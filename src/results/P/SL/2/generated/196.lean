

theorem Topology.P2_implies_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.P1_implies_frontier_subset_closure_interior (A := A) hP1