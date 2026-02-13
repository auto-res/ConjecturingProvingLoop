

theorem Topology.P3_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- The intersection of two open sets is open.
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_subset_interiorClosure (X := X) (A := A ∩ B) h_open