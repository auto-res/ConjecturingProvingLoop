

theorem interior_closure_interior_satisfies_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hP2 : Topology.P2 (interior (closure (interior A))) :=
    Topology.interior_closure_satisfies_P2 (A := interior A)
  exact Topology.P2_implies_P3 hP2