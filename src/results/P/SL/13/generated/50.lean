

theorem Topology.P2_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure (interior (A : Set X)))) := by
  have h_open : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) h_open