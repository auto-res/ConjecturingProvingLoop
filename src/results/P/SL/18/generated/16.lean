

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := Topology.P2_interior A
  exact Topology.P2_implies_P3 hP2