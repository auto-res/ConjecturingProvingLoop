

theorem all_Ps_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P3 A := by
  constructor
  · intro h
    exact h.2.2
  · intro hP3
    -- From `P3` and openness we obtain `P2`.
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).1 hP3
    -- `P2` implies `P1`.
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P2_implies_P1 (A := A) hP2
    exact And.intro hP1 (And.intro hP2 hP3)