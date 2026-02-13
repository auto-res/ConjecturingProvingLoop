

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : interior A ⊆ interior B := interior_mono hAB
  exact closure_mono hInt