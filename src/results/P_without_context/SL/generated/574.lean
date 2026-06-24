

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  intro hP2
  have hP1 : Topology.P1 (A := A) := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    exact interior_subset hx₁
  have hP3 : Topology.P3 (A := A) := by
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hmono : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have hx₂ : x ∈ interior (closure A) := (interior_mono hmono) hx₁
    exact hx₂
  exact And.intro hP1 hP3