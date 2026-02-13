

theorem Topology.P1_nonempty_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  classical
  -- First, show that `interior A` is non-empty.
  have hIntA : (interior A).Nonempty := by
    by_contra hIntEmpty
    have hIntEqEmpty : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClEmpty : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEqEmpty, closure_empty] using
        (closure_empty : closure (∅ : Set X) = ∅)
    rcases hA with ⟨x, hxA⟩
    have hxCl : x ∈ closure (interior A) := hP1 hxA
    have : False := by
      simpa [hClEmpty] using hxCl
    exact this
  -- Pick a point of `interior A`.
  rcases hIntA with ⟨y, hyInt⟩
  -- `interior A` is contained in `interior (closure (interior A))`.
  have hSubset : interior A ⊆ interior (closure (interior A)) := by
    have : interior A ⊆ closure (interior A) := subset_closure
    have := interior_mono this
    simpa [interior_interior] using this
  exact ⟨y, hSubset hyInt⟩