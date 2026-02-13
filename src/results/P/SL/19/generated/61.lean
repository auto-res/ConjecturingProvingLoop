

theorem Topology.P2_iff_closure_eq_closure_interior_and_subset {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) ↔
      (closure A = closure (interior A) ∧ A ⊆ interior (closure A)) := by
  have h₁ := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  have h₂ := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  constructor
  · intro hP2
    rcases h₂.1 hP2 with ⟨hP1, hP3⟩
    exact ⟨h₁.1 hP1, hP3⟩
  · rintro ⟨hEq, hSub⟩
    have hP1 : Topology.P1 (A := A) := h₁.2 hEq
    have hP3 : Topology.P3 (A := A) := hSub
    exact h₂.2 ⟨hP1, hP3⟩