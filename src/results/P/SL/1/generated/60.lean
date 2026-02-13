

theorem Topology.P2_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  -- The set `interior (closure (interior A))` is open, so it automatically satisfies `P2`.
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P2_of_isOpen (A := interior (closure (interior A))) hOpen