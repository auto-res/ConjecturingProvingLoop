

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
      ) = interior (closure A) := by
  -- Step 1: use the previously established four-step idempotence
  have h4 :
      interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure A) :=
    interior_closure_interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := A)
  -- Step 2: apply `interior ∘ closure` to both sides of `h4`
  have h5 :
      interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
        ) = interior (closure (interior (closure A))) :=
    congrArg (fun S : Set X => interior (closure S)) h4
  -- Step 3: finish with the two-step idempotence lemma
  calc
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
      ) = interior (closure (interior (closure A))) := by
        simpa using h5
    _ = interior (closure A) := by
        simpa using interior_closure_interior_closure_eq (X := X) (A := A)