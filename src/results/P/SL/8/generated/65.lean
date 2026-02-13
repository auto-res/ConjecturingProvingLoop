

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  have hInt : interior A ⊆ interior B := interior_mono hAB
  have hClos : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  exact interior_mono hClos