

theorem all_Ps_iff_P1_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P1 A := by
  constructor
  · intro h
    exact h.1
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P1_iff_P3_of_isOpen (A := A) hA).1 hP1
    exact And.intro hP1 (And.intro hP2 hP3)