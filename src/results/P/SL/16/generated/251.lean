

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A \ interior A : Set X) = (∅ : Set X) := by
  -- We prove that `interior (A \ interior A)` has no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxIntDiff
  -- `x` lies in `A \ interior A`.
  have hxDiff : x ∈ (A \ interior A : Set X) := interior_subset hxIntDiff
  -- Any open subset of `A` is contained in `interior A`.
  have h_subsetA : interior (A \ interior A : Set X) ⊆ A := by
    intro y hy
    exact (interior_subset hy).1
  have h_to_intA : interior (A \ interior A : Set X) ⊆ interior A :=
    interior_maximal h_subsetA isOpen_interior
  have hxIntA : x ∈ interior A := h_to_intA hxIntDiff
  -- Contradiction: `x` is both in and not in `interior A`.
  exact (hxDiff.2 hxIntA)