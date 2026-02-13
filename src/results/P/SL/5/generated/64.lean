

theorem P3_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : P3 (X := X) A) :
    closure (A : Set X) ⊆ closure (interior (closure A)) := by
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have hsubset : (A : Set X) ⊆ interior (closure A) := hA
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset