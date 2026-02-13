

theorem Topology.interiorClosure_satisfies_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure A)) h_open