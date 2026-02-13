

theorem P2_union_seven {X : Type*} [TopologicalSpace X]
    {A B C D E F G : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) := by
  -- Combine the first five sets.
  have hABCDE :
      Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P2_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P2 (X := X) (((A ∪ B ∪ C ∪ D ∪ E) ∪ F) ∪ G) :=
    Topology.P2_union (X := X)
      (A := (A ∪ B ∪ C ∪ D ∪ E) ∪ F) (B := G)
      hABCDEF hG
  -- Re‐associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCDEFG