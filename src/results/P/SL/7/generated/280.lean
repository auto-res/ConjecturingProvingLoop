

theorem Topology.eq_empty_of_P3_and_interiorClosure_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A)
    (hInt : interior (closure (A : Set X)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  classical
  by_cases hA : (A : Set X).Nonempty
  · -- `A` is nonempty: derive a contradiction with `hInt`.
    have hIntNe : (interior (closure (A : Set X))).Nonempty :=
      Topology.interiorClosure_nonempty_of_P3 (A := A) hP3 hA
    rcases hIntNe with ⟨x, hxInt⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hInt] using hxInt
    cases this
  · -- `A` is empty, as desired.
    simpa [Set.not_nonempty_iff_eq_empty] using hA