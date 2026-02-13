

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, combine the properties for `A`, `B`, and `C`.
  have hABC : Topology.P2 (X := X) (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Then, combine the result with `D`.
  have hABCD : Topology.P2 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCD