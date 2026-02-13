

theorem Topology.isOpen_iUnion_implies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, IsOpen (s i)) →
      (Topology.P1 (⋃ i, s i) ∧
        Topology.P2 (⋃ i, s i) ∧ Topology.P3 (⋃ i, s i)) := by
  intro hOpen
  have hP1 : Topology.P1 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P1 (s := s) hOpen
  have hP2 : Topology.P2 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P2 (s := s) hOpen
  have hP3 : Topology.P3 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P3 (s := s) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)