

theorem P2_nonempty_iff_interiorClosure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (interior (closure A)).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      Topology.P2_nonempty_interiorClosure (X := X) (A := A) hP2 hA
  · intro hInt
    by_cases hA : A.Nonempty
    · exact hA
    · -- Derive a contradiction from `hInt`
      have hA_eq : A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hIntEq : interior (closure A) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty, interior_empty]
      rcases hInt with ⟨x, hx⟩
      have hFalse : False := by
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hIntEq] using hx
        simpa using this
      exact False.elim hFalse