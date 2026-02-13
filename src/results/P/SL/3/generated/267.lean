

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  constructor
  · intro h
    -- From `P1 ∧ P3` obtain `P2` using the closedness of `A`.
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P2_iff_P1_and_P3_of_isClosed (A := A) hA_closed).2 h
    -- A closed set satisfies `P2` iff it is open.
    exact
      (Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP2
  · intro hOpen
    -- Any open set satisfies `P1` and `P3`.
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P1_of_isOpen (A := A) hOpen
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P3_of_isOpen (A := A) hOpen
    exact And.intro hP1 hP3