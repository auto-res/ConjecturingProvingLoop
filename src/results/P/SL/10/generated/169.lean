

theorem Topology.nonempty_interior_iff_nonempty_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hInt
    exact hInt.closure
  · intro hCl
    classical
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    ·
      have hIntEmpty : interior A = (∅ : Set X) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hInt
      have hContrad : False := by
        -- `hCl` gives a point in `closure (interior A)`, but this set is empty.
        have : (∅ : Set X).Nonempty := by
          simpa [hIntEmpty, closure_empty] using hCl
        simpa using this
      exact False.elim hContrad