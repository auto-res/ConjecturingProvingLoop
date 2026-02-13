

theorem Topology.P2_inter_three_of_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) (hC_closed : IsClosed C)
    (hA_P2 : Topology.P2 A) (hB_P2 : Topology.P2 B) (hC_P2 : Topology.P2 C) :
    Topology.P2 (A ∩ B ∩ C) := by
  -- First, obtain `P2` for the intersection `A ∩ B`.
  have hAB_P2 : Topology.P2 (A ∩ B) :=
    Topology.P2_inter_of_closed (X := X) (A := A) (B := B)
      hA_closed hB_closed hA_P2 hB_P2
  -- `A ∩ B` is closed, being the intersection of two closed sets.
  have hAB_closed : IsClosed (A ∩ B) := IsClosed.inter hA_closed hB_closed
  -- Intersect the result with `C`, using the two–set lemma once more.
  have hABC_P2 : Topology.P2 ((A ∩ B) ∩ C) :=
    Topology.P2_inter_of_closed (X := X) (A := A ∩ B) (B := C)
      hAB_closed hC_closed hAB_P2 hC_P2
  -- Rewrite the associative intersection to match the desired statement.
  simpa [Set.inter_assoc] using hABC_P2