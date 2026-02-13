

theorem interior_closure_interior_closure_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) :=
    isOpen_interior
  simpa using
    Topology.isOpen_imp_P3 (X := X)
      (A := interior (closure (interior (closure A)))) h_open