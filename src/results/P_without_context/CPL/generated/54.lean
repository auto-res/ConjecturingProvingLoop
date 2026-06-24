

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P1 A := by
  intro hP2
  exact subset_trans hP2 interior_subset

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P3 A := by
  intro hP2
  exact
    subset_trans hP2
      (interior_mono (closure_mono interior_subset))

theorem P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    -- `closure (interior A)` is contained in `closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    -- `closure A` is contained in `closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro hEq
    have h : A ⊆ closure A := subset_closure
    simpa [hEq.symm] using h

theorem P2_of_open {X : Type*} [TopologicalSpace X] (A : Set X) : IsOpen A → P2 A := by
  intro hOpen
  -- First, prove `interior A ⊆ interior (closure (interior A))`.
  have hSub : interior A ⊆ interior (closure (interior A)) := by
    have hInc : interior A ⊆ closure (interior A) := subset_closure
    simpa [interior_interior] using interior_mono hInc
  -- Turn this into the desired inclusion `A ⊆ …` using `hOpen.interior_eq`.
  exact by
    intro x hx
    have hx' : x ∈ interior A := by
      simpa [hOpen.interior_eq] using hx
    exact hSub hx'

theorem P3_of_open {X : Type*} [TopologicalSpace X] (A : Set X) : IsOpen A → P3 A := by
  intro hOpen
  intro x hx
  have hx' : x ∈ interior A := by
    simpa [hOpen.interior_eq] using hx
  have hSub : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact hSub hx'