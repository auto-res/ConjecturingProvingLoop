

theorem P3_interiors_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P3 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  exact P3_of_open (A := interior A ∪ interior B) h_open