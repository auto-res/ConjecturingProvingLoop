

theorem Topology.interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure (A ∩ B)) := by
  -- First, record the obvious inclusion between the underlying sets.
  have h_subset : A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    exact And.intro hxA (interior_subset hxIntB)
  -- Monotonicity of `closure` upgrades the inclusion.
  have h_closure : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Finally, pass to interiors using monotonicity once more.
  exact interior_mono h_closure