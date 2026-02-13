

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure (interior (closure A)))) := by
  apply P3_of_open
  simpa using isOpen_interior

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P2_imp_P3 hP2
  · intro hP3
    intro x hxA
    -- from `P3`, and using `closure_eq` for a closed set, we get `x ∈ interior A`
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      have h₁ : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      have h₂ := interior_mono h₁
      simpa [interior_interior] using h₂
    exact h_subset hx_intA

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P1 A ↔ P2 A := by
  constructor
  · intro hP1
    have hP3 : P3 (A := A) := P3_dense (A := A) hA
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    exact P2_imp_P1 (A := A) hP2