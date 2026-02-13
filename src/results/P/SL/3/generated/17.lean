

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (A : Set X))) := by
  have h : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.P3_of_isOpen (A := interior (closure A)) h)