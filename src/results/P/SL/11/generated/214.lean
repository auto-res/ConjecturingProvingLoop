

theorem P123_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      ((Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ∧
        (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B)) := by
  constructor
  · -- From the product triple, deduce triples for each factor.
    rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    -- Extract the `P1` properties.
    have hP1Factors :=
      (Topology.P1_prod_iff (A := A) (B := B) hA hB).1 hP1Prod
    rcases hP1Factors with ⟨hP1A, hP1B⟩
    -- Extract the `P2` properties.
    have hP2Factors :=
      (Topology.P2_prod_iff (A := A) (B := B) hA hB).1 hP2Prod
    rcases hP2Factors with ⟨hP2A, hP2B⟩
    -- Extract the `P3` properties.
    have hP3Factors :=
      (Topology.P3_prod_iff (A := A) (B := B) hA hB).1 hP3Prod
    rcases hP3Factors with ⟨hP3A, hP3B⟩
    -- Assemble the result.
    exact ⟨⟨hP1A, hP2A, hP3A⟩, ⟨hP1B, hP2B, hP3B⟩⟩
  · -- From triples for the factors, build the product triple.
    rintro ⟨hTripleA, hTripleB⟩
    exact
      Topology.P123_prod (A := A) (B := B) hTripleA hTripleB