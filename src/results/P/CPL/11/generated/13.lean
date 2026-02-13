

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  simpa using (P1_of_open (A := interior A) isOpen_interior)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  simpa using (P2_of_open (A := interior A) isOpen_interior)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  exact
    (interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior) hx

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  exact P1_closure (P1_of_P2 hA)