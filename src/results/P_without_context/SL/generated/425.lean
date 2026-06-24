

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  have hP1 : Topology.P1 (A := A) := by
    dsimp [Topology.P1, Topology.P2] at *
    exact subset_trans hA
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A))
  have hP3 : Topology.P3 (A := A) := by
    dsimp [Topology.P3, Topology.P2] at *
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
      have hcl : closure (interior A) ⊆ closure A := by
        have : interior A ⊆ A :=
          (interior_subset : interior A ⊆ A)
        exact closure_mono this
      exact interior_mono hcl
    exact subset_trans hA hsubset
  exact And.intro hP1 hP3