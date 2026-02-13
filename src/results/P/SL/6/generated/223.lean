

theorem all_Ps_iff_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2.1
  · intro hP2
    have hP1 : Topology.P1 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).2 hP2
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).2 hP2
    exact And.intro hP1 (And.intro hP2 hP3)