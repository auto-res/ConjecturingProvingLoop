

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact
    (interior_subset :
      (interior (closure (interior A)) : Set X) ⊆ closure (interior A))
      (h hx)

theorem closure_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : closure A = interior (closure A) := by
  apply subset_antisymm
  ·
    intro x hx
    have hxA : x ∈ A := by
      simpa [hA.closure_eq] using hx
    exact h hxA
  ·
    exact interior_subset

theorem P1_closed_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 A ↔ closure (interior A) = A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    have h_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    simpa [hA.closure_eq] using h_eq
  · intro h_eq
    intro x hx
    simpa [h_eq] using hx

theorem P2_iff_P3_for_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P3_of_P2 (A := A) hP2
  · intro hP3
    intro x hxA
    -- First, `x` lies in the interior of `A`
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- Show that `interior A ⊆ interior (closure (interior A))`
    have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      have h_sub : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h_sub
      simpa [interior_interior] using h_mono
    exact h_subset hx_intA

theorem P1_iff_dense_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    exact closure_interior_eq_of_P1 (A := A) hP1
  · intro h_eq
    intro x hx
    have : (x ∈ closure A) := subset_closure hx
    simpa [h_eq] using this

theorem exists_closed_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, IsClosed B ∧ B ⊆ A ∧ P1 B := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset A, ?_⟩
  intro x hx
  cases hx