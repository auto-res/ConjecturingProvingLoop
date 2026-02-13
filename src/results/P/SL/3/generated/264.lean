

theorem subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro x hxA
  -- Since `A` is open, `interior A = A`.
  have hxIntA : (x : X) ∈ interior (A : Set X) := by
    simpa [hA.interior_eq] using hxA
  -- Monotonicity of `interior` gives the desired inclusion.
  have hMono :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hMono hxIntA