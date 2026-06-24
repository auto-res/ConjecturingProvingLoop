

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact fun x hxA => hsubset (hP2 hxA)