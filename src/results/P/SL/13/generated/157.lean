

theorem Topology.P1_interiorClosureSet {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (A : Set X))) := by
  -- The set `interior (closure A)` is open.
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Any open set satisfies `P1`.
  exact
    Topology.isOpen_subset_closureInterior
      (X := X) (A := interior (closure (A : Set X))) h_open