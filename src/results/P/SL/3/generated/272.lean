

theorem Topology.nonempty_iff_interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact interior_nonempty_of_P2 (A := A) hA hP2
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩