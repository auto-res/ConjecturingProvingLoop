

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  -- Prove P1
  have hP1 : Topology.P1 A := by
    dsimp [Topology.P1]
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hx₂ : x ∈ closure (interior A) := interior_subset hx₁
    exact hx₂
  -- Prove P3
  have hP3 : Topology.P3 A := by
    dsimp [Topology.P3]
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hmono₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
    have hmono₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hmono₁
    have hx₂ : x ∈ interior (closure A) := hmono₂ hx₁
    exact hx₂
  exact And.intro hP1 hP3