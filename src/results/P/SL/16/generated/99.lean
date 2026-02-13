

theorem Topology.P2_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X := X) A)
    (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- We prove that `A` contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  -- `P2` puts points of `A` inside `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- But the hypothesis tells us this interior is empty.
  have hInt_eq : interior (closure (interior A)) = (∅ : Set X) := by
    simp [hIntEmpty]
  -- Hence `x` lies in the empty set, contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hInt_eq] using hxInt
  exact this.elim