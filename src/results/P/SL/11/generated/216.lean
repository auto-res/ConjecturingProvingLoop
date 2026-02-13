

theorem interior_closure_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, its closure and hence the given interior are empty,
      -- contradicting `hInt`.
      have hAeq : (A : Set X) = ∅ :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have : (interior (∅ : Set X)).Nonempty := by
        simpa [hAeq, closure_empty] using hInt
      simpa [interior_empty] using this
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P2 (A := A) hP2 hA