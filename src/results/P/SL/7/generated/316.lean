

theorem Topology.IsOpen_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (interior (closure (A : Set X))) := by
  simpa using isOpen_interior