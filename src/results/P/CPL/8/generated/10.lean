

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact closure_interior_eq_of_P1 (A := A) hP1
  · intro hEq
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    simpa [hEq] using hx_cl

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  have : x ∈ interior (closure (interior A)) := hsubset hx
  simpa [interior_interior] using this

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact closure_interior_eq_of_P1 (A := A) (P2_to_P1 (A := A) hP2)