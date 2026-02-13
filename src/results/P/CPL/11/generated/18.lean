

theorem closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : closure A = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hsubset : (A : Set X) ⊆ interior (closure A) := hA
    exact closure_mono hsubset
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hsubset : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    simpa using closure_mono hsubset

theorem interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : interior (closure (interior A)) = interior (closure A) := by
  -- From `P1 A` we get equality of the two closures
  have h_eq : closure (interior A) = closure A :=
    (P1_iff_closure_interior_eq).1 hA
  -- Taking interiors of both sides yields the desired result
  simpa using congrArg interior h_eq

theorem dense_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior A) = closure A := by
  exact (P1_iff_closure_interior_eq).1 (P1_of_P2 hA)