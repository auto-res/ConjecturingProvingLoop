

theorem closureInteriorClosureInteriorClosureInterior_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure (interior A)))))) := by
  have h_open :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X)
      (A := interior (closure (interior (closure (interior A))))) h_open