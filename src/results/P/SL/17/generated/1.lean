

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 Topology.P3 at *
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : interior A ⊆ A)
  exact h_mono hx₁