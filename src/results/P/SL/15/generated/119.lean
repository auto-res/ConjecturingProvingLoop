

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P1` property coordinate-wise.
  have hA' : p.1 ∈ closure (interior A) := hA hpA
  have hB' : p.2 ∈ closure (interior B) := hB hpB
  -- Identify the target closure set using `interior_prod_eq` and `closure_prod_eq`.
  have h_closure_prod :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa [interior_prod_eq] using
      (closure_prod_eq (s := interior A) (t := interior B))
  -- Conclude the desired membership.
  have : (p : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
    ⟨hA', hB'⟩
  simpa [h_closure_prod] using this