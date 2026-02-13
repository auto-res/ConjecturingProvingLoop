

theorem open_inter_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.open_satisfies_P3 (A := A ∩ B) hOpen