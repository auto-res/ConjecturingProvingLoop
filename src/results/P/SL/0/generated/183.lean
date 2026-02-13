

theorem inter_open_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hP1 := Topology.P1_inter_of_open (X := X) (A := A) (B := B) hA hB
  have hP2 := Topology.P2_inter_of_open (X := X) (A := A) (B := B) hA hB
  have hP3 := Topology.P3_inter_of_open (X := X) (A := A) (B := B) hA hB
  exact And.intro hP1 (And.intro hP2 hP3)