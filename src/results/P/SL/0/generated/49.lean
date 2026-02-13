

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P1 A := by
  intro hOpen
  exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).1