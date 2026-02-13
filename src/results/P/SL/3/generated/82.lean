

theorem P1_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using (P1_of_isOpen (A := A ∩ B) hOpen)