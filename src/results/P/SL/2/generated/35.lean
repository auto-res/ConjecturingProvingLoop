

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  exact (Topology.P1_closure_of_P1 (A := interior A)) (Topology.P1_interior (A := A))