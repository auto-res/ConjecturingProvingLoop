

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at *
  -- Take an arbitrary point `p` in `A ×ˢ B`
  intro p hp
  -- Break down the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P1` hypotheses on the two coordinates
  have hA_cl : p.1 ∈ closure (interior A) := hA hpA
  have hB_cl : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` lies in the product of the two closures
  have h_mem_prod :
      p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hA_cl, hB_cl⟩
  -- Identify this product with the closure of the product of interiors
  have h_closure_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) :=
    closure_prod_eq
  have h_mem_closure_prod :
      p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_closure_prod_eq] using h_mem_prod
  -- The product of the interiors is contained in the interior of the product
  have h_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    -- It is open …
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      isOpen_interior.prod isOpen_interior
    -- … and contained in `A ×ˢ B`
    have h_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hq1, hq2⟩
      exact And.intro (interior_subset hq1) (interior_subset hq2)
    -- Hence it lies inside the interior of the product
    exact interior_maximal h_sub h_open
  -- Take closures to pass to the desired set
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset
  -- Conclude
  exact h_closure_subset h_mem_closure_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Unfold `P2`
  dsimp [Topology.P2] at *
  intro p hp
  -- Split the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the hypotheses on the two coordinates
  have h1 : p.1 ∈ interior (closure (interior A)) := hA hpA
  have h2 : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- `p` belongs to the following open product
  have h_mem :
      p ∈
        Set.prod (interior (closure (interior A)))
                 (interior (closure (interior B))) :=
    ⟨h1, h2⟩
  -- Show that this product is contained in
  -- `closure (interior (A ×ˢ B))`
  have h_subset :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Move each coordinate inside the corresponding closure
    have hq1_cl : q.1 ∈ closure (interior A) := interior_subset hq1
    have hq2_cl : q.2 ∈ closure (interior B) := interior_subset hq2
    -- Hence `q` lies in the product of the two closures
    have hq_prod :
        q ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this product with a closure of a product
    have h_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) :=
      closure_prod_eq
    have hq_closure :
        q ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_prod_eq] using hq_prod
    -- `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`
    have h_sub_prod :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      -- The product of interiors is open …
      have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
        isOpen_interior.prod isOpen_interior
      -- … and contained in `A ×ˢ B`
      have h_sub :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro r hr
        exact And.intro (interior_subset hr.1) (interior_subset hr.2)
      -- Apply `interior_maximal`
      exact interior_maximal h_sub h_open
    -- Take closures
    have h_closure_sub :
        closure (Set.prod (interior A) (interior B)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_sub_prod
    -- Conclude the desired inclusion
    exact h_closure_sub hq_closure
  -- The product we built is open
  have h_open_prod :
      IsOpen (Set.prod (interior (closure (interior A)))
                       (interior (closure (interior B)))) :=
    isOpen_interior.prod isOpen_interior
  -- Therefore it is contained in the *interior* of the target set
  have h_sub_interior :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) :=
    interior_maximal h_subset h_open_prod
  -- Apply this inclusion to `p`
  exact h_sub_interior h_mem

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Unfold `P3`
  dsimp [Topology.P3] at *
  intro p hp
  -- Decompose the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P3` hypotheses on the two coordinates
  have h1 : p.1 ∈ interior (closure A) := hA hpA
  have h2 : p.2 ∈ interior (closure B) := hB hpB
  -- Hence `p` lies in the product of the two interiors
  have h_mem :
      p ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    ⟨h1, h2⟩
  -- The product of the interiors is open
  have h_open :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) :=
    isOpen_interior.prod isOpen_interior
  -- Show that this product is contained in the closure of `A ×ˢ B`
  have h_sub_closure :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate is in the corresponding closure
    have hq1_cl : q.1 ∈ closure A := interior_subset hq1
    have hq2_cl : q.2 ∈ closure B := interior_subset hq2
    -- So `q` lies in the product of closures
    have hq_prod : q ∈ Set.prod (closure A) (closure B) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this set with the closure of the product
    have h_eq : closure (Set.prod A B) = Set.prod (closure A) (closure B) :=
      closure_prod_eq
    simpa [h_eq] using hq_prod
  -- By maximality of the interior, we can pass to the interior
  have h_sub_interior :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        interior (closure (Set.prod A B)) :=
    interior_maximal h_sub_closure h_open
  -- Conclude for our point `p`
  exact h_sub_interior h_mem

theorem P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : Topology.P1 A ↔ Topology.P3 A := by
  -- Obtain `P2 A` from the density hypothesis
  have hP2 : Topology.P2 (A := A) :=
    Topology.P2_of_dense_interior (A := A) h_dense
  -- Extract `P1 A ∧ P3 A` from `P2 A`
  have hP1P3 : Topology.P1 A ∧ Topology.P3 A :=
    ((Topology.P2_iff_P1_and_P3 (A := A)).1 hP2)
  -- Build the desired equivalence
  exact
    ⟨
      -- Forward implication: `P1 A → P3 A`
      fun _ => (Topology.P2_implies_P3 (A := A) hP2),
      -- Backward implication: `P3 A → P1 A`
      fun _ => hP1P3.1
    ⟩

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at *
  intro y hy
  -- Obtain a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the `P3` hypothesis to `x`
  have hx : x ∈ interior (closure A) := hA hxA
  -- Map this membership through the homeomorphism
  have hx_img : (e x : Y) ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
  -- `e` transports interiors and closures
  have h_int_eq := e.image_interior (s := closure A)
  have h_cl_eq  := e.image_closure  (s := A)
  -- Rewrite the membership step by step
  have h1 : (e x : Y) ∈ interior (e '' closure A) := by
    simpa [h_int_eq] using hx_img
  have h2 : (e x : Y) ∈ interior (closure (e '' A)) := by
    simpa [h_cl_eq] using h1
  exact h2