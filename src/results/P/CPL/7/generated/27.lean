

theorem P2_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Use `P2` on each coordinate.
  have hx : p.1 ∈ interior (closure (interior A)) := hA hpA
  have hy : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- Define suitable open neighbourhoods.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hU_open : IsOpen U := isOpen_interior
  have hV_open : IsOpen V := isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  have hpUV : p ∈ (U ×ˢ V : Set (X × Y)) := by
    dsimp [U, V] at *
    exact And.intro hx hy
  --------------------------------------------------------------------
  --  Show `U ×ˢ V ⊆ closure (interior (A ×ˢ B))`.
  --------------------------------------------------------------------
  have h_subset_closure :
      (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Upgrade to closures of the interiors.
    have hq1 : q.1 ∈ closure (interior A) := interior_subset hqU
    have hq2 : q.2 ∈ closure (interior B) := interior_subset hqV
    have hq_prod :
        (q : X × Y) ∈
          (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) :=
      And.intro hq1 hq2
    -- Rewrite with `closure_prod_eq`.
    have hq_cl :
        (q : X × Y) ∈
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa [closure_prod_eq] using hq_prod
    -- `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_interior_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      -- Basic inclusion.
      have h_basic :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro r hr
        rcases hr with ⟨hrA, hrB⟩
        exact And.intro (interior_subset hrA) (interior_subset hrB)
      -- Openness of the product.
      have h_open :
          IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
        isOpen_interior.prod isOpen_interior
      exact interior_maximal h_basic h_open
    -- Taking closures preserves inclusions.
    have h_closure_subset :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_interior_subset
    exact h_closure_subset hq_cl
  --------------------------------------------------------------------
  --  Since `U ×ˢ V` is open, it is contained in the interior
  --  of the above closure.
  --------------------------------------------------------------------
  have h_subset_int :
      (U ×ˢ V : Set (X × Y)) ⊆
        interior (closure (interior (A ×ˢ B))) :=
    interior_maximal h_subset_closure hUV_open
  exact h_subset_int hpUV