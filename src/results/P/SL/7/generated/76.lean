

theorem Topology.P2_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact IsOpen_P2 (A := interior (closure (interior A))) hOpen