

theorem P2_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∪ interior B) := by
  simpa using (Topology.P123_interior_union (A := A) (B := B)).2.1