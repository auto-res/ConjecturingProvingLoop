

theorem Topology.isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ Topology.P2 A) := by
  intro hOpen
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P2 (A := A) hOpen
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2