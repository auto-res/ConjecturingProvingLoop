

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  dsimp [Topology.P1, Topology.P2, Topology.P3] at *
  have hP1 : A ⊆ closure (interior A) :=
    subset_trans h interior_subset
  have hcl : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h2 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hcl
  have hP3 : A ⊆ interior (closure A) :=
    subset_trans h h2
  exact And.intro hP1 hP3