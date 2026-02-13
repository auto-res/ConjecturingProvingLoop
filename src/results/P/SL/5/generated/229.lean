

theorem P1_union_seven {X : Type*} [TopologicalSpace X] {A B C D E F G : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) := by
  -- Combine the properties for the first six sets.
  have hABCDEF :
      Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) :=
    Topology.P1_union_six (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      hA hB hC hD hE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F) (B := G)
      hABCDEF hG
  -- Re‐associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFG