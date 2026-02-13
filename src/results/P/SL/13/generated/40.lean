

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure (A : Set X))) := by
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure (A : Set X))) h_open