

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact
      ⟨Topology.P2_implies_P1 (A := A) hP2,
        Topology.P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    intro x hxA
    have hx₁ : x ∈ interior (closure A) := hP3 hxA
    have hsubset : interior (closure A) ⊆ interior (closure (interior A)) := by
      have hcl : closure A ⊆ closure (interior A) :=
        Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
      exact interior_mono hcl
    exact hsubset hx₁