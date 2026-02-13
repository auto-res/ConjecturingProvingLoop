

theorem Topology.interiorClosureClosure_eq_interiorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]