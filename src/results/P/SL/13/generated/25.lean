

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (A : Set X)) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  exact Topology.isOpen_subset_interiorClosure (X := X) (A := interior A) h_open