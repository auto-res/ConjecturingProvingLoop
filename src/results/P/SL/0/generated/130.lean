

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  -- First, use monotonicity of `interior` on the inclusion `A ⊆ B`.
  have hInt : (interior (A : Set X) : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Next, apply `closure_mono` to obtain an inclusion between the closures.
  have hCl :
      closure (interior (A : Set X)) ⊆
        closure (interior (B : Set X)) := closure_mono hInt
  -- Finally, apply `interior_mono` once more to the previous inclusion.
  exact interior_mono hCl