

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior A ⊆ A) hxInt⟩
  · intro hA
    exact Topology.interior_nonempty_of_P1 (A := A) hP1 hA