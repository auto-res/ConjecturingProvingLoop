

theorem interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  -- First, `interior` is monotone with respect to set inclusion.
  have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Taking closures preserves inclusions.
  have hClos :
      closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono hInt
  -- Finally, `interior` is again monotone.
  exact interior_mono hClos