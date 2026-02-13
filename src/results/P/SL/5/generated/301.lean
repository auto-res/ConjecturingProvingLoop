

theorem P1_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H)
    (hI : Topology.P1 (X := X) I) (hJ : Topology.P1 (X := X) J) :
    Topology.P1 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) := by
  -- First, combine the properties for the first nine sets.
  have hNine :
      Topology.P1 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) :=
    Topology.P1_union_nine (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I)
      hA hB hC hD hE hF hG hH hI
  -- Unite the result with `J`.
  have hTen :
      Topology.P1 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) (B := J)
      hNine hJ
  -- Re-associate the unions to match the required expression.
  simpa [Set.union_assoc] using hTen