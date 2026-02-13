

theorem Topology.P1_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P1_interiorClosure (A := A))