

theorem all_Ps_iff_P2_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2.1
  · intro hP2
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P2_implies_P1_of_closed (A := A) hA hP2
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3_of_closed (A := A) hA hP2
    exact And.intro hP1 (And.intro hP2 hP3)