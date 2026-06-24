

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A ∧ Topology.P3 A := by
  intro hP2
  have hP1 : Topology.P1 A := by
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact subset_trans hP2 hsubset
  have hP3 : Topology.P3 A := by
    have hclosure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have hinterior : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hclosure
    exact subset_trans hP2 hinterior
  exact And.intro hP1 hP3