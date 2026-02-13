

theorem P1_nested_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure (interior (A : Set X)))))) := by
  -- The set under consideration is an interior, hence open.
  have hOpen :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  -- Any open set satisfies `P1`.
  simpa using
    (Topology.P1_of_isOpen
      (A := interior (closure (interior (closure (interior A))))) hOpen)