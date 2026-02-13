

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hP2 : Topology.P2 (interior (closure A)) :=
    Topology.P2_interior_closure A
  exact Topology.P2_implies_P3 hP2