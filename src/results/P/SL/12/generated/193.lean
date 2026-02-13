

theorem Topology.P3_union_of_P2_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Upgrade the `P2` hypothesis on `A` to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  -- Combine the `P3` properties using the union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := B) hA3 hB