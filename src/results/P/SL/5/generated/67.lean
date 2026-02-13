

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  exact closure_mono (interior_mono (closure_mono hAB))