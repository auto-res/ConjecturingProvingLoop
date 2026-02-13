

theorem interior_frontier_eq_empty_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    interior (frontier A) = (∅ : Set X) := by
  -- Rewrite the frontier using the fact that `A` is closed.
  have hFrontier : (frontier A : Set X) = A \ interior A :=
    frontier_eq_diff_interior_of_closed (A := A) hA
  -- Show that `interior (A \ interior A)` is empty.
  have hEmpty : interior (A \ interior A : Set X) = (∅ : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      -- `x ∈ A \ interior A`
      have hxDiff : x ∈ A \ interior A := interior_subset hx
      -- `x ∈ interior A`, since interiors are monotone and
      -- `(A \ interior A) ⊆ A`.
      have hSub : (A \ interior A : Set X) ⊆ A := by
        intro y hy; exact hy.1
      have hxIntA : x ∈ interior A := (interior_mono hSub) hx
      -- Contradiction with `x ∉ interior A`.
      exact (hxDiff.2 hxIntA).elim
    · exact Set.empty_subset _
  -- Use the two identities obtained above.
  calc
    interior (frontier A)
        = interior (A \ interior A) := by
          simpa [hFrontier]
    _   = (∅ : Set X) := hEmpty