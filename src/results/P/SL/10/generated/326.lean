

theorem Topology.P3_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior A ∪ interior B) := by
  -- Both `interior A` and `interior B` are open,
  -- hence their union is open as well.
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  -- Open sets satisfy `P3`.
  exact
    Topology.isOpen_implies_P3
      (X := X)
      (A := interior A ∪ interior B)
      h_open