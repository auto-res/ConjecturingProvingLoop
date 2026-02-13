

theorem P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have h := Topology.P123_inter_open (A := A) (B := B) hA hB
  exact h.2.1