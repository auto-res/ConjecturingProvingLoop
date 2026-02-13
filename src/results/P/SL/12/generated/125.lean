

theorem Topology.P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- First upgrade `P2` to `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Then invoke the closed‐set lemma turning `P3` into `P1`.
  exact
    Topology.P3_implies_P1_of_isClosed
      (X := X) (A := A) h_closed hP3