

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P2 A := by
  intro hOpen
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen
  exact hAll.2.1