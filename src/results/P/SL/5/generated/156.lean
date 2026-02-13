

theorem P3_union_six {X : Type*} [TopologicalSpace X] {A B C D E F : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) := by
  -- First, combine the properties for the first five sets.
  have hABCDE :
      Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P3_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Re-associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEF