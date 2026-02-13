

theorem Topology.P2_interior_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior (closure (interior A))))) := by
  have h_open :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure (interior (closure (interior A)))))
      h_open