

theorem isOpen_inter_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hP1 : Topology.P1 (A ∩ B) :=
    isOpen_inter_imp_P1 (X := X) (A := A) (B := B) hA hB
  have hP2 : Topology.P2 (A ∩ B) :=
    isOpen_inter_imp_P2 (X := X) (A := A) (B := B) hA hB
  have hP3 : Topology.P3 (A ∩ B) :=
    isOpen_inter_imp_P3 (X := X) (A := A) (B := B) hA hB
  exact And.intro hP1 (And.intro hP2 hP3)