

theorem interior_closure_interior_closure_has_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    (Topology.isOpen_implies_P1
        (X := X)
        (A := interior (closure (interior (closure A))))) hOpen