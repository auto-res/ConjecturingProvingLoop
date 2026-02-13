

theorem Topology.not_P1_of_nonempty_emptyInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : A.Nonempty) (hIntEmpty : interior A = (∅ : Set X)) :
    ¬ Topology.P1 (X := X) A := by
  intro hP1
  -- From `P1` and `hA`, the interior of `A` must be nonempty.
  have hIntNon : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- But this contradicts the hypothesis that the interior is empty.
  simpa [hIntEmpty] using hIntNon