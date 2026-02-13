

theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔
      interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`
    have hsubset :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    -- Show that `interior A` has no elements.
    refine Set.eq_empty_iff_forall_not_mem.2 ?_
    intro x hxIntA
    have : (x : X) ∈ interior (closure (interior A)) := hsubset hxIntA
    simpa [h] using this
  · intro hIntEmpty
    -- From `interior A = ∅` we get `closure (interior A) = ∅`.
    have hClIntEmpty : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty]
    -- Hence its interior is also empty.
    simpa [hClIntEmpty] using by
      simp [hClIntEmpty]