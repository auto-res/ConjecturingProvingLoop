

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have hInt : interior (closure A) ⊆ interior (closure B) :=
    interior_closure_mono (X := X) (A := A) (B := B) hAB
  exact closure_mono hInt