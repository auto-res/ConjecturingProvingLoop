

theorem Topology.P3_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P3_interiorClosure (A := A))