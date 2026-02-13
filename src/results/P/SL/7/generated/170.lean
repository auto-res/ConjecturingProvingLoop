

theorem Topology.interiorClosureInterior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔
      interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence it must also be empty.
    have hSub : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) :=
        (Topology.interior_subset_interiorClosureInterior (A := A)) hx
      simpa [h] using this
    -- Use `Subset.antisymm` to obtain the desired equality.
    apply Set.Subset.antisymm
    · exact hSub
    · intro x hx
      cases hx
  · intro hInt
    -- From `interior A = ∅` we derive
    -- `closure (interior A) = ∅` and hence its interior is also `∅`.
    have hClosure : closure (interior A) = (∅ : Set X) := by
      simpa [hInt] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))
    simpa [hClosure] using
      (interior_empty : interior (∅ : Set X) = (∅ : Set X))