

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior (A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int
  exact h₂ (h₁ hx)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA_open
  intro x hx
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA_open
  have hx' : x ∈ interior (closure A) := h_subset hx
  simpa [hA_open.interior_eq] using hx'