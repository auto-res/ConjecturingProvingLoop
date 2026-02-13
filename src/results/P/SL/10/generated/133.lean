

theorem Topology.P1_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior).union isOpen_interior
  exact
    Topology.isOpen_implies_P1 (X := X) (A := interior A ∪ interior B) h_open