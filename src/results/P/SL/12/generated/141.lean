

theorem Topology.P1_P2_P3_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- `P1` follows from the combination of closedness and openness of `A`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_isClosed_isOpen (X := X) (A := A) h_closed h_open
  -- `P2` holds for any open set.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) h_open
  -- `P3` is equivalent to openness for closed sets, hence holds as well.
  have hP3 : Topology.P3 (X := X) A := by
    have h_equiv := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
    exact (h_equiv.mpr h_open)
  exact And.intro hP1 (And.intro hP2 hP3)