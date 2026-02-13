

theorem Topology.P2_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P2_interiorClosure (A := closure (A : Set X)))