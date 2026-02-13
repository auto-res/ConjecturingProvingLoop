

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsub :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  have hx' : x ∈ interior (closure (interior A)) := hsub hx
  simpa [interior_interior] using hx'

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 (closure (interior A)) := by
  intro hP2
  intro x hx
  have hx_clA : x ∈ closure (A : Set X) :=
    (closure_mono (interior_subset : (interior A : Set X) ⊆ A)) hx
  have h_clA_subset : closure (A : Set X) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hP2
  exact h_clA_subset hx_clA

theorem closure_inter_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) ⊆ closure A := by
  intro _
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)