

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  unfold Topology.P2 at h
  unfold Topology.P1
  have h' : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact h.trans h'