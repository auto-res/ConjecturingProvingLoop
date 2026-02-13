

theorem Topology.P2_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact
    Topology.P3_implies_frontier_subset_closure_interior_closure
      (A := A) hP3