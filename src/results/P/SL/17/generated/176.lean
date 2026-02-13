

theorem Topology.P2_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  -- Swap the roles of `A` and `B` and reuse the existing left‐hand variant.
  have h := Topology.P2_inter_isOpen_left (A := B) (B := A) hOpenB hP2A
  simpa [Set.inter_comm] using h