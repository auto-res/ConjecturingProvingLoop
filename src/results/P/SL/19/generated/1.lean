

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact (interior_mono hsubset) hx₁