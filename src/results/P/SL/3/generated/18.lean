

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (A : Set X))) := by
  have h : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using (Topology.P2_of_isOpen (A := interior (closure (A : Set X))) h)