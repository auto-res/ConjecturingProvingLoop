

theorem P3_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using (Topology.P3_of_isOpen (A := A ∩ B) hOpen)