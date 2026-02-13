

theorem P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P2 A := by
  exact (Topology.P123_of_isClopen (A := A) hClopen).2.1