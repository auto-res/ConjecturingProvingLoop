

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  -- Prove P1
  have hP1 : Topology.P1 A := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hx₂ : x ∈ closure (interior A) := (interior_subset) hx₁
    exact hx₂
  -- Prove P3
  have hP3 : Topology.P3 A := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hcl_subset : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hcl_subset
    exact h_int_subset hx₁
  exact And.intro hP1 hP3