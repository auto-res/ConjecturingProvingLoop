

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (closure (A : Set X))).Nonempty) :
    (A : Set X).Nonempty := by
  classical
  by_contra hA
  -- If `A` were empty, so would be `interior (closure A)`, contradicting `h`.
  have hAeq : (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hA
  have hIntEq : interior (closure (A : Set X)) = (∅ : Set X) := by
    simpa [hAeq] using by
      simp
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hIntEq] using h
  rcases hNonemptyEmpty with ⟨x, hx⟩
  exact hx