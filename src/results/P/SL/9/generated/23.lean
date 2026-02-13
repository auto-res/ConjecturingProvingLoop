

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (A := interior (closure A)) := by
  exact Topology.P3_of_isOpen (A := interior (closure A)) isOpen_interior