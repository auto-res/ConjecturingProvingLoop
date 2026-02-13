

theorem open_inter_satisfies_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- Open sets satisfy `P1`.
  exact Topology.open_satisfies_P1 (A := A ∩ B) hOpen