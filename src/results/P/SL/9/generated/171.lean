

theorem Topology.P1_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A := A ∩ B ∩ C) := by
  -- The intersection of three open sets is open.
  have h_open : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    exact IsOpen.inter hAB hC
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A ∩ B ∩ C) h_open