

theorem Topology.interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, pass to interiors using monotonicity.
  have h₁ : interior A ⊆ interior B := interior_mono hAB
  -- Next, take closures, preserving the inclusion.
  have h₂ : closure (interior A) ⊆ closure (interior B) := closure_mono h₁
  -- Finally, take interiors again to obtain the desired inclusion.
  exact interior_mono h₂