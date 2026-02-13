

theorem Topology.P3_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P3_inter_isOpen_left (A := B) (B := A) hOpenB hP3A)