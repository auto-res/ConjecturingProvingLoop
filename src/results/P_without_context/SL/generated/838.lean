

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    exact interior_subset hx₁
  have hP3 : Topology.P3 A := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hcl : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    have hint : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hcl
    exact hint hx₁
  exact And.intro hP1 hP3