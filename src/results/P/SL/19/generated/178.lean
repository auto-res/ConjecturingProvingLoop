

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A \ interior A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A \ interior A`
    have hxDiff : x ∈ A \ interior A := interior_subset hx
    -- Any open subset of `A` is contained in `interior A`
    have hSubInt :
        (interior (A \ interior A) : Set X) ⊆ interior A := by
      -- First, `interior (A \ interior A)` is contained in `A`
      have hSubA :
          (interior (A \ interior A) : Set X) ⊆ A := fun y hy =>
        (interior_subset hy).1
      -- Use the maximality of the interior
      exact interior_maximal hSubA isOpen_interior
    -- Therefore `x ∈ interior A`
    have hxInt : x ∈ interior A := hSubInt hx
    -- Contradiction with `x ∉ interior A`
    exact (hxDiff.2 hxInt).elim
  · exact Set.empty_subset _