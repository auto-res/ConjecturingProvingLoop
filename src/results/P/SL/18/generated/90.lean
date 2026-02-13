

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hP2 : Topology.P2 (interior (closure (interior A))) :=
    Topology.P2_interior_closure_interior A
  exact Topology.P2_implies_P3 hP2