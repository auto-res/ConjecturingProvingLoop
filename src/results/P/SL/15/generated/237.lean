

theorem closure_interior_four_iter_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- Define the iteration `F` := closure ∘ interior.
  let F : Set X → Set X := fun S ↦ closure (interior S)
  -- Idempotence: `F (F S) = F S`.
  have h_id : ∀ S : Set X, F (F S) = F S := by
    intro S
    simpa [F] using
      (closure_interior_closure_interior_closure_eq (X := X) (A := S))
  -- Apply idempotence successively to collapse four iterations to one.
  have h1 : F (F (F (F A))) = F (F (F A)) := by
    simpa [F] using h_id (F (F A))
  have h2 : F (F (F A)) = F (F A) := by
    simpa [F] using h_id (F A)
  have h3 : F (F A) = F A := by
    simpa [F] using h_id A
  have h_final : F (F (F (F A))) = F A := by
    calc
      F (F (F (F A))) = F (F (F A)) := h1
      _ = F (F A) := h2
      _ = F A := h3
  -- Unfold `F` to obtain the desired equality.
  simpa [F] using h_final