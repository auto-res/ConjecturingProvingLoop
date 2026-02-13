

theorem Topology.interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  -- Pick a point `x ∈ A`.
  rcases hA with ⟨x, hxA⟩
  -- `P2` sends this point inside `interior (closure (interior A))`.
  have hxIntCl : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Either `interior A` is nonempty or it is empty.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · -- If `interior A` is empty, derive a contradiction with `hxIntCl`.
    -- First, record this emptiness.
    have hIntEmpty : interior A = (∅ : Set X) := by
      apply (Set.eq_empty_iff_forall_not_mem).2
      intro y hy
      have : (interior A).Nonempty := ⟨y, hy⟩
      exact (hInt this).elim
    -- Then `interior (closure (interior A))` is also empty.
    have hIntClEmpty : interior (closure (interior A)) = (∅ : Set X) := by
      simp [hIntEmpty]
    -- But `x` was assumed to lie in this empty set—contradiction.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntClEmpty] using hxIntCl
    cases this