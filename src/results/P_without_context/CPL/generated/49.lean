

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (h hx)

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  classical
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure (interior A) ⊆ closure A`
      have h : interior A ⊆ A := interior_subset
      exact closure_mono h
    · -- `closure A ⊆ closure (interior A)`
      have h : A ⊆ closure (interior A) := hP1
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
      simpa [closure_closure] using h'
  · intro hEq
    -- From `closure (interior A) = closure A` we get `A ⊆ closure (interior A)`
    simpa [hEq.symm] using (subset_closure : (A : Set X) ⊆ closure A)