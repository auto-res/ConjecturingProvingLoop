

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  intro x hx
  -- `P1 A` yields `closure A ⊆ closure (interior A)`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- First enlarge with `closure_mono`, then simplify.
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using this
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- We also have `interior A ⊆ interior (closure A)`.
  have h₂ : interior A ⊆ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono h_subset
  -- Taking closures preserves this inclusion.
  have h₃ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h₂
  exact h₃ hx₁

theorem P1_compl_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 Aᶜ := by
  have hOpen : IsOpen (Aᶜ) := h_closed.isOpen_compl
  exact open_implies_P1 hOpen

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  exact P1_and_P3_implies_P2 ⟨h1, h3⟩