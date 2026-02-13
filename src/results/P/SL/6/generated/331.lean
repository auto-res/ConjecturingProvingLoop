

theorem nonempty_iff_nonempty_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      nonempty_interior_closure_of_nonempty_P3 (A := A) hP3 hA
  · intro hInt
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · exfalso
      -- From `¬ A.Nonempty`, deduce `interior (closure A)` is empty,
      -- contradicting `hInt`.
      have hIntEq :
          interior (closure (A : Set X)) = (∅ : Set X) := by
        have hAeq : (A : Set X) = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hA
        simpa [hAeq, closure_empty, interior_empty]
      rcases hInt with ⟨x, hx⟩
      simpa [hIntEq] using hx