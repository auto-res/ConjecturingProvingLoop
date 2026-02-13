

theorem Topology.P3_union_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Upgrade the `P2` hypotheses to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  have hB3 : Topology.P3 (X := X) B :=
    Topology.P2_implies_P3 (X := X) (A := B) hB
  -- Apply the union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hA3 hB3