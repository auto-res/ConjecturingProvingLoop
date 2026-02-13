

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) :
    Topology.P2 (X := X) (A ∪ B ∪ C) := by
  -- First combine `A` and `B`.
  have hAB : Topology.P2 (X := X) (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Then union the result with `C`.
  have hABC : Topology.P2 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC