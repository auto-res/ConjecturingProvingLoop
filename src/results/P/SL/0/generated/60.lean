

theorem isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hOpen
  dsimp [Topology.P1]
  -- Step 1:  Show `A ⊆ interior (closure A)`.
  have hA_sub : (A : Set X) ⊆ interior (closure (A : Set X)) := by
    intro x hxA
    -- Since `A` is open, `x` is an interior point of `A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      simpa [hOpen.interior_eq] using hxA
    -- Monotonicity of `interior` gives the desired inclusion.
    have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact hMono hxIntA
  -- Step 2: Take closures to obtain the required inclusion.
  have hClosure :
      (closure (A : Set X) : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hA_sub
  exact hClosure