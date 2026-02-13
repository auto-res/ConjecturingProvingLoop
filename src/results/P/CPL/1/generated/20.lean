

theorem P3_iff_P2_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa using
    (P3_iff_P1_for_open (A := A) hA).trans
      (P1_iff_P2_for_open (A := A) hA)

theorem P1_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (⊤ : Set X)) : P1 A := by
  intro x hx
  simpa [h] using (by
    simp : x ∈ (⊤ : Set X))

theorem P3_of_dense_int_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = (⊤ : Set X)) : P3 A := by
  intro x hx
  have : (x : X) ∈ (⊤ : Set X) := by
    simp
  simpa [h] using this