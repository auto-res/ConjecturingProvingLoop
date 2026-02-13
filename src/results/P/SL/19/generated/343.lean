

theorem Topology.interior_union_interiors_eq_union_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  have hOpen : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  simpa using hOpen.interior_eq