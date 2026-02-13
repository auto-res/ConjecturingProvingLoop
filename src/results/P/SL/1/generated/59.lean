

theorem Topology.P3_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) hOpen