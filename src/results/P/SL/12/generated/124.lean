

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure B)) := by
  -- Step 1: Enlarge `closure A` to `closure B` using monotonicity of `closure`.
  have h₁ : (closure (A : Set X)) ⊆ closure B := closure_mono hAB
  -- Step 2: Apply monotonicity of `interior` to the previous inclusion.
  have h₂ : (interior (closure (A : Set X)) : Set X) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Step 3: Take closures of both sides to obtain the desired inclusion.
  exact closure_mono h₂