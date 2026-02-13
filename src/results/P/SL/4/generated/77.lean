

theorem P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, since it is an interior.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_P3 (A := interior (closure (interior (closure A)))) hOpen