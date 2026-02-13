

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (A : Set X))) := by
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact
    Topology.isOpen_subset_interiorClosure
      (X := X) (A := interior (closure (A : Set X))) h_open