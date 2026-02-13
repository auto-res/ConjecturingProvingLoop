

theorem P2_iff_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro h2
    exact ⟨P1_of_P2 h2, P3_of_P2 h2⟩
  · rintro ⟨h1, h3⟩
    intro x hx
    have hx3 : x ∈ interior (closure A) := h3 hx
    have h_eq : interior (closure (interior A)) = interior (closure A) :=
      interior_closure_eq_of_P1 h1
    simpa [h_eq] using hx3

theorem P3_of_open_dense_subset {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) (h_dense : closure U = closure A) (h_sub : A ⊆ U) : P3 A := by
  intro x hxA
  -- `A ⊆ U`, hence `x ∈ U`
  have hxU : x ∈ U := h_sub hxA
  -- Because `U` is open and contained in `closure A`, we have `U ⊆ interior (closure A)`.
  have hU_interior : (U : Set X) ⊆ interior (closure A) := by
    -- First, show `U ⊆ closure A`.
    have hU_closure : (U : Set X) ⊆ closure A := by
      -- We always have `U ⊆ closure U`; rewrite using `h_dense`.
      have : (U : Set X) ⊆ closure U := subset_closure
      simpa [h_dense] using this
    exact interior_maximal hU_closure hU
  -- Conclude that `x ∈ interior (closure A)`.
  exact hU_interior hxU

theorem interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : interior (closure (interior A)) = interior (closure A) := by
  simpa using interior_closure_eq_of_P1 (P1_of_P2 hA)