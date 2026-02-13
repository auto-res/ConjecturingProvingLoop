

theorem Topology.P1_of_subset_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBsub : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  intro x hxB
  -- Step 1: from the assumption `B ⊆ closure (interior A)` obtain
  --         that `x` lies in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior A) := hBsub hxB
  -- Step 2: monotonicity of `interior` for the inclusion `A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Step 3: taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Step 4: combine the facts to obtain the desired conclusion.
  exact hCl hx_clA