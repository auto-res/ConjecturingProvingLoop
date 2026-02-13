

theorem P1_union_six {X : Type*} [TopologicalSpace X] {A B C D E F : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) := by
  -- Combine the properties for the first five sets.
  have hABCDE :
      Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P1_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCDEF