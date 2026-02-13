

theorem Topology.P2_emptyInteriorClosureInterior_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A)
    (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this.elim