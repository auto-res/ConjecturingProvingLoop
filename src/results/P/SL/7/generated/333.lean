

theorem Topology.IsOpen_P1_P2_P3_inter_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) ∧ Topology.P2 (A ∩ B ∩ C) ∧ Topology.P3 (A ∩ B ∩ C) := by
  have hOpen : IsOpen (A ∩ B ∩ C) := ((hA.inter hB).inter hC)
  simpa using Topology.IsOpen_P1_P2_P3 (A := A ∩ B ∩ C) hOpen