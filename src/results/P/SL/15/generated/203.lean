

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  have h_int : interior A ⊆ interior B := interior_mono hAB
  have h_closure : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int
  exact interior_mono h_closure