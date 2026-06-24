

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_sub : closure (interior A) ⊆ closure A := by
    have h_int_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_int_subset
  have h_int_sub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_sub
  exact h_int_sub hx₁