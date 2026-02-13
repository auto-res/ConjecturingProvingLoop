

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have h_intA : interior A = A := hA.interior_eq
  have h_subset : (A : Set X) ⊆ interior (closure A) := by
    have h : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    simpa [h_intA] using h
  simpa [h_intA] using h_subset hx

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  exact
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
      (by simpa [hA.interior_eq] using hx)

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  intro x hx
  exact
    (interior_mono (closure_mono (interior_subset : interior A ⊆ A))) (h hx)

theorem closure_interior_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure (interior A) = closure A := by
  apply subset_antisymm
  · exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  ·
    have : closure A ⊆ closure (interior A) := by
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
      simpa [closure_closure] using h'
    simpa using this

theorem P2_iff_P1_for_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = (⊤ : Set X)) : P2 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    -- P2 ⇒ P1
    intro x hx
    exact interior_subset (hP2 hx)
  · intro hP1
    -- P1 ⇒ P2, using density
    intro x hx
    have h_closure : (closure (interior A) : Set X) = ⊤ := by
      have h_eq : closure (interior A) = closure A :=
        closure_interior_eq_of_P1 (A := A) hP1
      simpa [hA] using h_eq
    simpa [h_closure, interior_univ] using (by
      simp : x ∈ (⊤ : Set X))

theorem interior_eq_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P2 A) : interior A = A := by
  -- We prove both inclusions to establish equality.
  apply Set.Subset.antisymm
  · -- `interior A ⊆ A` is always true.
    exact interior_subset
  · -- For the reverse inclusion we use `h : A ⊆ interior (closure (interior A))`
    -- together with the fact that `closure (interior A) ⊆ A` when `A` is closed.
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    -- Since `A` is closed, `closure A = A`.
    have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
      have : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [hA.closure_eq] using this
    -- `interior` is monotone, so we can pass from the previous subset to interiors.
    have : interior (closure (interior A)) ⊆ interior A :=
      interior_mono h_closure_subset
    exact this hx'