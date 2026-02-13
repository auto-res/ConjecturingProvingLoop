

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (interior A) := by
  simpa using openSet_P1 (X := X) (A := interior A) isOpen_interior

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Obtain `P1` and `P3` for the individual factors
  have hP1A : Topology.P1 A := P2_implies_P1 (A := A) hA
  have hP1B : Topology.P1 B := P2_implies_P1 (A := B) hB
  have hP3A : Topology.P3 A := P2_implies_P3 (A := A) hA
  have hP3B : Topology.P3 B := P2_implies_P3 (A := B) hB
  ----------------------------------------------------------------
  -- `P3` for the product
  ----------------------------------------------------------------
  have hP3_prod : Topology.P3 (Set.prod A B) := P3_prod hP3A hP3B
  ----------------------------------------------------------------
  -- `P1` for the product
  ----------------------------------------------------------------
  have hP1_prod : Topology.P1 (Set.prod A B) := by
    dsimp [Topology.P1] at hP1A hP1B ⊢
    intro p hp
    rcases hp with ⟨hpA, hpB⟩
    -- Coordinates lie in the corresponding closures
    have hx : p.1 ∈ closure (interior A) := hP1A hpA
    have hy : p.2 ∈ closure (interior B) := hP1B hpB
    -- Hence the point lies in the product of the two closures
    have h_prod_closure :
        (p : X × Y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hx, hy⟩
    -- Identify this product with a closure of a product
    have h_closure_eq :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    have h_in_closure_prod :
        (p : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_closure_eq] using h_prod_closure
    ----------------------------------------------------------------
    -- The closure above is contained in `closure (interior (A × B))`
    ----------------------------------------------------------------
    have h_prod_subset :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- Basic inclusion into `A × B`
      have h_simple :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨ha, hb⟩
        exact ⟨interior_subset ha, interior_subset hb⟩
      -- The set on the left is open
      have h_open : IsOpen (Set.prod (interior A) (interior B)) := by
        have h1 : IsOpen (interior A) := isOpen_interior
        have h2 : IsOpen (interior B) := isOpen_interior
        simpa using h1.prod h2
      exact interior_maximal h_simple h_open
    have h_closure_subset :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_prod_subset
    exact h_closure_subset h_in_closure_prod
  ----------------------------------------------------------------
  -- Combine `P1` and `P3` via the characterisation of `P2`
  ----------------------------------------------------------------
  exact
    (P2_iff_P1_and_P3 (A := Set.prod A B)).2 ⟨hP1_prod, hP3_prod⟩

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (e ⁻¹' B) := by
  -- Step 1: identify the preimage with an image under `e.symm`
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  -- Step 2: apply the image lemma for `e.symm`
  have hP1_image : Topology.P1 (e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  simpa [h_eq] using hP1_image

theorem P2_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ A = interior (closure (interior A)) := by
  --------------------------------------------------------------------
  -- Auxiliary inclusion : `interior (closure (interior A)) ⊆ A`
  -- (it uses that `A` is closed).
  --------------------------------------------------------------------
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆ A := by
    intro x hx
    -- first, `x ∈ closure (interior A)`
    have hx_cl_int : x ∈ closure (interior A) := interior_subset hx
    -- monotonicity of `closure`
    have hx_clA : x ∈ closure A :=
      (closure_mono (interior_subset : (interior A : Set X) ⊆ A)) hx_cl_int
    -- since `A` is closed, `closure A = A`
    simpa [hA.closure_eq] using hx_clA
  --------------------------------------------------------------------
  -- Establish the equivalence.
  --------------------------------------------------------------------
  constructor
  · -- `P2 A → A = interior (closure (interior A))`
    intro hP2
    exact Set.Subset.antisymm hP2 h_subset
  · -- `A = interior (closure (interior A)) → P2 A`
    intro h_eq
    dsimp [Topology.P2]
    intro x hxA
    -- rewrite the membership using the given equality
    exact (h_eq ▸ hxA)