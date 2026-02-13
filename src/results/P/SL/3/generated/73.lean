

theorem Topology.P3_iff_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- A closed set satisfying P3 is open, by a previous lemma.
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
    -- For open sets, P3 and P2 are equivalent.
    have hEquiv := Topology.P3_iff_P2_of_isOpen (A := A) hOpen
    exact hEquiv.mp hP3
  · intro hP2
    -- In general, P2 implies P3.
    exact Topology.P2_implies_P3 (A := A) hP2