

theorem Topology.P1_P2_P3_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hClopen
  have hOpen : IsOpen A := hClopen.2
  exact Topology.P1_P2_P3_of_isOpen (A := A) hOpen