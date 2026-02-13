

theorem P1_open_iff_closure_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → (P1 A ↔ P1 (closure A)) := by
  intro hA_open
  constructor
  · intro hP1
    exact P1_closure (A := A) hP1
  · intro _
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    simpa [hA_open.interior_eq] using hx_cl