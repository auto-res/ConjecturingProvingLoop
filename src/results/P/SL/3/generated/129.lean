

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  exact closure_mono (interior_mono (closure_mono hAB))