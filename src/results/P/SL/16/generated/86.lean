

theorem Topology.isOpen_inter_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (X := X) (A ∩ B) ∧
    Topology.P2 (X := X) (A ∩ B) ∧
    Topology.P3 (X := X) (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A ∩ B) hOpen