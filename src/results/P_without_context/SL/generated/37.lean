

theorem P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsubset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono hsubset
  exact subset_trans hP2 hmono