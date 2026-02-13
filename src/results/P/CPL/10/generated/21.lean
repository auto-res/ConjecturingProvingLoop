

theorem exists_countable_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Set.Countable A ∧ Topology.P2 A := by
  exact ⟨(∅ : Set X), Set.countable_empty, Topology.P2_empty (X := X)⟩

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  classical
  -- Useful inclusions relating `A`, its interior, and the closure of its interior
  have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
    have : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hA.closure_eq] using this
  have h_int_subset : (interior (closure (interior A)) : Set X) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset_int : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- Prove the equivalence
  constructor
  · -- `P2 → P3`
    intro hP2
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hx₂ : x ∈ interior A := h_int_subset hx₁
    simpa [hA.closure_eq] using hx₂
  · -- `P3 → P2`
    intro hP3
    intro x hx
    have hx₁ : x ∈ interior (closure A) := hP3 hx
    have hx_intA : x ∈ interior A := by
      simpa [hA.closure_eq] using hx₁
    exact h_subset_int hx_intA