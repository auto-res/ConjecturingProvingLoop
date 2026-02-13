

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      IsOpen (A : Set X) := by
  constructor
  · intro h
    -- Extract `P2 A` from the triple.
    have hP2 : Topology.P2 (X := X) A := h.2.1
    -- Convert `P2 A` to openness using the closed‐set equivalence.
    exact
      (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP2
  · intro h_open
    -- For an open set, all three properties hold.
    exact Topology.P1_P2_P3_of_isOpen (X := X) (A := A) h_open