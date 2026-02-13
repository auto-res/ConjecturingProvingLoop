

theorem Topology.nonempty_iff_interior_nonempty_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact interior_nonempty_of_P1 (A := A) hA hP1
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩