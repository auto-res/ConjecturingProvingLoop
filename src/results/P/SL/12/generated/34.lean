

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First enlarge `interior A` to `interior B` using monotonicity of `interior`.
  have h₁ : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Then enlarge the closures accordingly.
  have h₂ : closure (interior A : Set X) ⊆ closure (interior B) :=
    closure_mono h₁
  -- Finally, take interiors once more to get the desired inclusion.
  exact interior_mono h₂