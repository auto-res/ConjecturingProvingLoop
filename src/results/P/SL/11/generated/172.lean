

theorem not_P2_of_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior A = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P2 A := by
  intro hP2
  have hInt : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P2 (A := A) hP2 hne
  simpa [hIntEmpty] using hInt