

theorem Topology.isOpen_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (A : Set X))) := by
  exact isOpen_interior