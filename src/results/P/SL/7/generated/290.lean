

theorem Topology.eq_empty_of_P1_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior A = (∅ : Set X) → A = (∅ : Set X) := by
  classical
  intro hP1 hIntEmpty
  by_cases hA : (A : Set X).Nonempty
  · -- If `A` is non-empty, `P1` yields a contradiction with `interior A = ∅`.
    have hIntNonempty : (interior A).Nonempty :=
      Topology.interior_nonempty_of_P1 (A := A) hP1 hA
    rcases hIntNonempty with ⟨x, hx⟩
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEmpty] using hx
    exact (by cases this)
  · -- Otherwise `A` is empty, as desired.
    simpa [Set.not_nonempty_iff_eq_empty] using hA