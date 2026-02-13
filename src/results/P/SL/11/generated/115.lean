

theorem P2_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  -- Extract `P1` and `P3` for `A` from the given `P2` assumption.
  have hP1A : Topology.P1 A := Topology.P2_implies_P1 (A := A) hA
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 (A := A) hA
  -- Obtain `P1` and `P3` for the intersection using the existing lemmas.
  have hP1 : Topology.P1 (A ∩ B) :=
    Topology.P1_inter_right_open (A := A) (B := B) hP1A hB_open
  have hP3 : Topology.P3 (A ∩ B) :=
    Topology.P3_inter_right_open (A := A) (B := B) hP3A hB_open
  -- Combine `P1` and `P3` to conclude `P2` for the intersection.
  exact Topology.P2_of_P1_and_P3 (A := A ∩ B) ⟨hP1, hP3⟩