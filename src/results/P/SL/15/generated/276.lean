

theorem isOpen_closure_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  have hClosure : (closure A : Set X) = (Set.univ : Set X) :=
    denseInterior_implies_closure_eq_univ (X := X) (A := A) hDense
  simpa [hClosure] using isOpen_univ