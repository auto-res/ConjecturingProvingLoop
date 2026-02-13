

theorem P3_union_eight {X : Type*} [TopologicalSpace X] {A B C D E F G H : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F)
    (hG : Topology.P3 (X := X) G) (hH : Topology.P3 (X := X) H) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) := by
  -- First, combine the properties for the first seven sets.
  have hABCDEFG :
      Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) :=
    Topology.P3_union_seven (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
      hA hB hC hD hE hF hG
  -- Unite the result with `H`.
  have hABCDEFGH :
      Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) (B := H)
      hABCDEFG hH
  -- Re-associate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFGH