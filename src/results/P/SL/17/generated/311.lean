

theorem Topology.nonempty_interior_closure_interior_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (interior A))).Nonempty ↔ (interior A).Nonempty := by
  -- First, translate the desired statement into a comparison of (in)equality
  -- with the empty set, using `Set.nonempty_iff_ne_empty`.
  have hNe :
      (interior (closure (interior A)) ≠ (∅ : Set X)) ↔
        interior A ≠ (∅ : Set X) := by
    -- Take the negation of the equivalence of emptiness already proved.
    have hEmpty :=
      Topology.interior_closure_interior_eq_empty_iff (A := A)
    exact (not_congr hEmpty)
  -- Rewrite `Nonempty` in terms of `≠ ∅` and conclude.
  simpa [Set.nonempty_iff_ne_empty] using hNe