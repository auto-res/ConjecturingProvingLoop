

theorem closure_interior_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    (closure (interior (A : Set X))).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hInt
    -- If `interior A` is empty, its closure is also empty,
    -- contradicting the assumed non‐emptiness.
    have hIntEmpty : interior (A : Set X) = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    have hClEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using rfl
    have hNonemptyEmpty : (∅ : Set X).Nonempty := by
      simpa [hClEmpty] using hCl
    rcases hNonemptyEmpty with ⟨x, hx⟩
    cases hx
  · intro hInt
    exact
      Topology.closure_interior_nonempty_of_interior_nonempty
        (X := X) (A := A) hInt