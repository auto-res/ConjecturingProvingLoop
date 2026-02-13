

theorem interior_closure_interior_closure_has_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  -- The set `interior (closure (interior (closure A)))` is open, so it satisfies `P2`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  have hAll :=
    Topology.isOpen_has_all_Ps
      (X := X) (A := interior (closure (interior (closure A)))) hOpen
  exact hAll.2.1