

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have hcl : closure (interior A) ⊆ closure (interior B) := by
    apply closure_mono
    exact interior_mono hAB
  exact (interior_mono hcl) hx