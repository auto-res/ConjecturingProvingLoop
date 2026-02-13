

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) :
    Topology.P1 (X := X) (A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, union the result with `C`.
  have hABC : Topology.P1 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite via associativity of union.
  simpa [Set.union_assoc] using hABC