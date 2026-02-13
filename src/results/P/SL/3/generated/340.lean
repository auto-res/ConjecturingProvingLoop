

theorem P3_interior_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure (interior (closure (A : Set X))))))) := by
  -- The set is an interior of something, hence open.
  have hOpen :
      IsOpen (interior (closure (interior (closure (interior (closure (A : Set X))))))) := by
    simpa using isOpen_interior
  -- Any open set satisfies `P3`.
  simpa using
    (Topology.P3_of_isOpen
      (A := interior (closure (interior (closure (interior (closure (A : Set X))))))) hOpen)