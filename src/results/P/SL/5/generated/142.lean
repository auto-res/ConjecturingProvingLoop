

theorem P2_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- First, combine `A`, `B`, `C`, and `D`.
  have hABCD : Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P2_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Unite the result with `E`.
  have hABCDE : Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Re-associate unions to match the required shape.
  simpa [Set.union_assoc] using hABCDE