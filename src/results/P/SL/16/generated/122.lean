

theorem Topology.not_P2_of_nonempty_emptyInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : A.Nonempty) (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    ¬ Topology.P2 (X := X) A := by
  intro hP2
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this.elim