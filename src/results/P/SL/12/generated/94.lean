

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) :
    Topology.P3 (X := X) (A ∪ B ∪ C) := by
  -- First, union `A` and `B`.
  have hAB : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC