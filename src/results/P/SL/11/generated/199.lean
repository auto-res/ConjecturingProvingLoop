

theorem interior_closure_nonempty_iff_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    -- `closure A` is nonempty because its interior is.
    have hCl : (closure A).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, (interior_subset : interior (closure A) ⊆ closure A) hx⟩
    -- Either `A` is nonempty or we derive a contradiction.
    by_cases hA : A.Nonempty
    · exact hA
    · -- If `A` were empty, its closure would be empty, contradicting `hCl`.
      have hAeq : (A : Set X) = ∅ :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hFalse : False := by
        have : (∅ : Set X).Nonempty := by
          simpa [hAeq, closure_empty] using hCl
        rcases this with ⟨x, hx⟩
        exact hx
      exact (False.elim hFalse)
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hA