

theorem P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    (Topology.P1_of_isOpen (A := interior (closure (interior A))) hOpen)