

theorem Topology.P2_inter_open_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    IsOpen A → IsOpen B → IsOpen C → Topology.P2 (A ∩ B ∩ C) := by
  intro hA hB hC
  have hOpen : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := hA.inter hB
    exact hAB.inter hC
  exact IsOpen_P2 (A := A ∩ B ∩ C) hOpen