

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  -- Unfold `P1` in the hypotheses and in the goal
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the coordinate‐wise hypotheses
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` belongs to the product of the two closures
  have h_prod :
      (p : X × Y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    And.intro hx hy
  -- Identify the latter with a closure of a product
  have h_closure_prod :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using
      (closure_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)))
  have hp_in_closure :
      (p : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_closure_prod] using h_prod
  ----------------------------------------------------------------
  -- Inclusion of the open rectangle into `interior (A × B)`
  ----------------------------------------------------------------
  have h_subset :
      (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
        interior (Set.prod A B) := by
    -- Basic inclusion into `A × B`
    have h_basic :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hqa, hqb⟩
      exact ⟨interior_subset hqa, interior_subset hqb⟩
    -- The rectangle is open
    have h_open : IsOpen (Set.prod (interior A) (interior B)) := by
      have h1 : IsOpen (interior A) := isOpen_interior
      have h2 : IsOpen (interior B) := isOpen_interior
      simpa using h1.prod h2
    -- Apply maximality of the interior
    exact interior_maximal h_basic h_open
  -- Monotonicity of closures
  have h_closure_subset :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset
  exact h_closure_subset hp_in_closure

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (interior A) := by
  simpa using openSet_P2 (X := X) (A := interior A) isOpen_interior

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  simpa using (P2_iff_P1_and_P3 (A := A)).2 ⟨h1, h3⟩