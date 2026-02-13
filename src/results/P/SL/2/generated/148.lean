

theorem Topology.isOpen_inter_implies_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B → Topology.P1 (A ∩ B) := by
  intro hOpenA hOpenB
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  exact Topology.isOpen_implies_P1 (A := A ∩ B) hOpenInter