

theorem nonempty_of_closure_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (closure (interior (A : Set X))).Nonempty) : (A : Set X).Nonempty := by
  classical
  by_contra hA
  -- From `¬A.Nonempty`, deduce `A = ∅`.
  have hAempty : (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hA
  -- Hence `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = (∅ : Set X) := by
    simpa [hAempty] using interior_empty
  -- Consequently, its closure is also empty.
  have hClEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
    simpa [hIntEmpty] using closure_empty
  -- This contradicts the assumed non-emptiness.
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hClEmpty] using h
  rcases hNonemptyEmpty with ⟨x, hx⟩
  cases hx