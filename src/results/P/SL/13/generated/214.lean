

theorem Topology.P1_interiorClosureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior (closure (A : Set X))))) := by
  -- The set under consideration is an interior, hence it is open.
  have h_open :
      IsOpen (interior (closure (interior (closure (A : Set X))))) :=
    isOpen_interior
  -- Every open set satisfies `P1`.
  exact
    Topology.isOpen_subset_closureInterior
      (X := X)
      (A := interior (closure (interior (closure (A : Set X))))) h_open