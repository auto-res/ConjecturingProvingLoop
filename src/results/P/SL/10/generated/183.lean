

theorem Topology.interior_union_interior_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  simpa using h_open.interior_eq