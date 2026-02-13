

theorem Topology.P3_union_interior_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (interior A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_interior_right (X := X) (A := B) (B := A) hB)