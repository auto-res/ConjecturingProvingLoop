

theorem P1_inter_of_open_and_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP1B : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  have h := Topology.P1_inter_of_P1_and_open (A := B) (B := A) hP1B hOpenA
  simpa [Set.inter_comm] using h