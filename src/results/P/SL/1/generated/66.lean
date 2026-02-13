

theorem Topology.P1_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  -- The set `interior (closure (interior A))` is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P1_of_isOpen (A := interior (closure (interior A))) hOpen