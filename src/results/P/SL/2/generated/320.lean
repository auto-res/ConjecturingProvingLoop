

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    frontier (A : Set X) ⊆ closure (B : Set X) := by
  intro x hxFront
  -- `x` lies in the closure of `A` by definition of the frontier.
  have hxClA : (x : X) ∈ closure (A : Set X) :=
    (Topology.frontier_subset_closure (A := A)) hxFront
  -- Monotonicity of `closure` for the inclusion `A ⊆ B`.
  have hClSub : (closure (A : Set X)) ⊆ closure (B : Set X) :=
    closure_mono hAB
  exact hClSub hxClA