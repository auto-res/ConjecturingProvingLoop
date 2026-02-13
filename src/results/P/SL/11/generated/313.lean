

theorem P123_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  rcases hA with ⟨hP1A, hP2A, hP3A⟩
  have hP1Union : Topology.P1 (A ∪ B) :=
    Topology.P1_union_right_open (A := A) (B := B) hP1A hB_open
  have hP2Union : Topology.P2 (A ∪ B) :=
    Topology.P2_union_right_open (A := A) (B := B) hP2A hB_open
  have hP3Union : Topology.P3 (A ∪ B) :=
    Topology.P3_union_right_open (A := A) (B := B) hP3A hB_open
  exact ⟨hP1Union, hP2Union, hP3Union⟩