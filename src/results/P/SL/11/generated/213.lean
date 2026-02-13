

theorem not_P1_of_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior A = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P1 A := by
  intro hP1
  have hIntNonempty : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hne
  simpa [hIntEmpty] using hIntNonempty