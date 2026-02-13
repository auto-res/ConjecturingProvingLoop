

theorem Topology.P1_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty] using hx_cl
  exact this