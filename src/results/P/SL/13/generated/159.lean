

theorem Topology.interior_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ B := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  simpa using h_open.interior_eq