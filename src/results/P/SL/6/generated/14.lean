

theorem interior_closure_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hP2 : Topology.P2 (interior (closure A)) :=
    Topology.interior_closure_satisfies_P2 (A := A)
  exact Topology.P2_implies_P3 hP2