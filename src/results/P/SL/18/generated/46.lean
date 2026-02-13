

theorem P123_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  simpa using Topology.P123_of_open hOpenInter