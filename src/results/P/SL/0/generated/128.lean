

theorem interior_closure_interior_closure_has_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, hence it satisfies `P3`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := interior (closure (interior (closure A))))
        hOpen).2.2