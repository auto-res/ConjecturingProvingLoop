

theorem P3_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- Combine the first four sets.
  have hABCD : Topology.P3 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P3_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Unite the result with `E`.
  have hABCDE : Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P3_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Reassociate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDE