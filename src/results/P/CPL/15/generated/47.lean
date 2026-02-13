

theorem exists_closed_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : ∃ K, IsClosed K ∧ K ⊆ A ∧ P3 K := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, ?_⟩
  exact P3_empty (X := X)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using (P1_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P1_of_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior A) : P1 A := by
  intro x hx
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  have hx_int : (x : X) ∈ interior A := h hx_cl
  exact subset_closure hx_int

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃₀ {S | ∃ i, S = A i}) := by
  exact
    P2_sUnion (X := X) (ℬ := {S | ∃ i, S = A i})
      (by
        intro S hS
        rcases hS with ⟨i, rfl⟩
        exact h i)

theorem P1_dense_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : closure (e '' A) = closure (interior (e '' A)) := by
  have h : P1 (e '' A) := P1_image_of_homeomorph (e := e) (A := A) hA
  simpa using (closure_eq_of_P1 (A := e '' A) h)