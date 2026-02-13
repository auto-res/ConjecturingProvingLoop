

theorem P123_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h :
      ∀ B, B ∈ A →
        Topology.P1 (B : Set X) ∧ Topology.P2 (B : Set X) ∧ Topology.P3 (B : Set X)) :
    Topology.P1 (⋃₀ A) ∧ Topology.P2 (⋃₀ A) ∧ Topology.P3 (⋃₀ A) := by
  classical
  -- Extract the individual properties from the combined assumption.
  have hP1 : ∀ B, B ∈ A → Topology.P1 (B : Set X) := fun B hBA => (h B hBA).1
  have hP2 : ∀ B, B ∈ A → Topology.P2 (B : Set X) := fun B hBA => (h B hBA).2.1
  have hP3 : ∀ B, B ∈ A → Topology.P3 (B : Set X) := fun B hBA => (h B hBA).2.2
  -- Apply the existing `sUnion` lemmas component-wise.
  have h₁ : Topology.P1 (⋃₀ A) :=
    Topology.P1_sUnion (A := A) (by
      intro B hBA
      exact hP1 B hBA)
  have h₂ : Topology.P2 (⋃₀ A) :=
    Topology.P2_sUnion (A := A) (by
      intro B hBA
      exact hP2 B hBA)
  have h₃ : Topology.P3 (⋃₀ A) :=
    Topology.P3_sUnion (A := A) (by
      intro B hBA
      exact hP3 B hBA)
  exact ⟨h₁, h₂, h₃⟩