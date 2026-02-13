

theorem P2_interiors_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P2 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  exact P2_of_open (A := interior A ∪ interior B) h_open