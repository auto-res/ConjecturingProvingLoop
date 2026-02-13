

theorem isOpen_inter_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using Topology.isOpen_imp_P1 (X := X) (A := A ∩ B) hOpen