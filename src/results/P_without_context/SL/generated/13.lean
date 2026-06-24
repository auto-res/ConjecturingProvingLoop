

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono h_closure
  exact h_mono hx'