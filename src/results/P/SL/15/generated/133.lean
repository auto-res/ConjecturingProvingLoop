

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)