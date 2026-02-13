

theorem interior_closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  intro hDense
  -- First, use the existing result about the closure being all of `univ`.
  have h_closure :
      closure (interior (closure A)) = (Set.univ : Set X) :=
    closure_interior_closure_eq_univ_of_dense (X := X) (A := A) hDense
  -- Taking interiors on both sides yields the desired equality.
  calc
    interior (closure (interior (closure A)))
        = interior (Set.univ : Set X) := by
          simpa [h_closure]
    _ = (Set.univ : Set X) := by
          simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq