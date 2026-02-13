

theorem Topology.P3_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (interior (A : Set X)))) := by
  -- The set `interior (closure (interior A))` is open.
  have h_open : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
  -- Any open set satisfies `P3`.
  exact
    Topology.isOpen_subset_interiorClosure
      (X := X) (A := interior (closure (interior (A : Set X)))) h_open