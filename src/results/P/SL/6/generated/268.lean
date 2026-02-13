

theorem nonempty_iff_nonempty_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) :
    A.Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact nonempty_interior_of_nonempty_P1 (A := A) hP1 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩