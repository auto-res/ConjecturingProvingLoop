

theorem Topology.interiorClosureInterior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) ∧
    Topology.P2 (interior (closure (interior A))) ∧
    Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure (interior A))) h_open