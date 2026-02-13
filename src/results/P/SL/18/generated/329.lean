

theorem P123_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  rcases hClopen with ⟨hClosed, hOpen⟩
  simpa using Topology.P123_of_clopen (A := A) hOpen hClosed