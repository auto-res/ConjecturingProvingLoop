

theorem closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)