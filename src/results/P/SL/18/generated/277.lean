

theorem P2_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P2_inter_open_right (A := B) (B := A) hP2B hOpenA)