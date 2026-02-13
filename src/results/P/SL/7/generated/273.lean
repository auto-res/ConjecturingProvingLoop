

theorem Topology.P1_P2_P3_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
      Topology.P2 (interior (closure (interior A))) ∧
      Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.IsOpen_P1_P2_P3 (A := interior (closure (interior A))) hOpen