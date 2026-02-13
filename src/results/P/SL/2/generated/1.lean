

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl
  exact hsubset hx₁