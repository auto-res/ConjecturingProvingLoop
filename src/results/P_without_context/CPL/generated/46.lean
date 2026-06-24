

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  dsimp [P2]
  intro x hxA
  have hInt : interior A = A := hA.interior_eq
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hxA
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  have hx' : x ∈ interior (closure A) := hsubset hxInt
  simpa [hInt] using hx'

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2, P3] at *
  intro x hxA
  have hx₀ := hP2 hxA
  exact (interior_mono (closure_mono interior_subset)) hx₀

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx

theorem closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  · exact closure_minimal h isClosed_closure
  · exact closure_mono interior_subset

theorem interior_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior (closure A) = interior (closure (interior A)) := by
  have h_closure : closure A = closure (interior A) :=
    closure_eq_closure_interior (P2_implies_P1 h)
  simpa [h_closure]

theorem exists_subset_open_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B : Set X, A ⊆ B ∧ IsOpen B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), ?_, isOpen_univ, ?_⟩
  · intro _ _
    trivial
  · simpa using (P2_of_open (X := X) (A := (Set.univ : Set X)) isOpen_univ)