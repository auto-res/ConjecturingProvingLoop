

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro h
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hx_intA : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  have hx_int_closA : x ∈ interior (closure A) := hsubset hx_intA
  simpa [hA.interior_eq] using hx_int_closA

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  exact P3_of_P2 (P2_of_open hA)

theorem P1_and_P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ P2 A → P3 A := by
  rintro ⟨_, hP2⟩
  exact P3_of_P2 hP2