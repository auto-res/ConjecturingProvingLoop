

theorem P1_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) :
    Topology.P1 B → Topology.P1 (A ∩ B) := by
  intro hP1B
  have h := Topology.P1_inter_open (A := B) (B := A) hOpenA hP1B
  simpa [Set.inter_comm] using h