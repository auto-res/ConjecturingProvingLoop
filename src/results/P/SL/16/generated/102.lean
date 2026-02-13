

theorem Topology.P3_emptyInteriorClosure_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (X := X) A)
    (hIntEmpty : interior (closure A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this