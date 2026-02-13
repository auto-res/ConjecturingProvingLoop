

theorem P1_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- First, combine the properties for `A`, `B`, `C`, and `D`.
  have hABCD : Topology.P1 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P1_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Then, unite the result with `E`.
  have hABCDE : Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Re-associate the unions to match the target expression.
  simpa [Set.union_assoc] using hABCDE