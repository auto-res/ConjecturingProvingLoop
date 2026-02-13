

theorem nonempty_iff_nonempty_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact nonempty_interior_of_nonempty_P2 (A := A) hP2 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩