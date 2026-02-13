

theorem Topology.P3_union_three_of_P2 {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : Topology.P2 (X := X) A)
    (hB : Topology.P2 (X := X) B) (hC : Topology.P2 (X := X) C) :
    Topology.P3 (X := X) (A ∪ B ∪ C) := by
  -- Upgrade each `P2` hypothesis to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  have hB3 : Topology.P3 (X := X) B :=
    Topology.P2_implies_P3 (X := X) (A := B) hB
  have hC3 : Topology.P3 (X := X) C :=
    Topology.P2_implies_P3 (X := X) (A := C) hC
  -- First union `A` and `B`.
  have hAB3 : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA3 hB3
  -- Then union the result with `C`.
  have hABC3 : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB3 hC3
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC3