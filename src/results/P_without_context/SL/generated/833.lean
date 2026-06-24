

theorem Topology.P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A ∧ Topology.P3 A := by
  intro h
  constructor
  ·
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact subset_trans h h₁
  ·
    have h₂ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h₃ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h₂
    exact subset_trans h h₃