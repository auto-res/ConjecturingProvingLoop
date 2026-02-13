

theorem P1_and_P3_iff_subset_inter {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      (A ⊆ closure (interior A) ∩ interior (closure A)) := by
  constructor
  · intro h
    exact
      subset_inter_of_P1_and_P3 (X := X) (A := A) h.1 h.2
  · intro hSub
    have hP1 : Topology.P1 (X := X) A := by
      dsimp [Topology.P1] at *
      intro x hxA
      exact (hSub hxA).1
    have hP3 : Topology.P3 (X := X) A := by
      dsimp [Topology.P3] at *
      intro x hxA
      exact (hSub hxA).2
    exact ⟨hP1, hP3⟩