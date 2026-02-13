

theorem Topology.P2_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P2_of_isOpen (A := A ∩ B) hOpen)