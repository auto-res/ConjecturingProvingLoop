

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (A := interior (closure A)) := by
  exact Topology.P2_of_isOpen (A := interior (closure A)) isOpen_interior