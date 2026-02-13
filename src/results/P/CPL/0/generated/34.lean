

theorem P1_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  -- Split the point `p` and the membership conditions.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Use the `P1` hypotheses on the two coordinates.
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hy_cl : y ∈ closure (interior B) := hP1B hyB
  ------------------------------------------------------------------
  -- 1.  Show `(x, y)` belongs to `closure (interior A ×ˢ interior B)`.
  ------------------------------------------------------------------
  have h_mem_closure_S :
      (x, y) ∈ closure (Set.prod (interior A) (interior B)) := by
    -- First, note that `(x, y)` lies in the product of the two closures.
    have h_in_prod :
        (x, y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      And.intro hx_cl hy_cl
    -- Identify that product with the required closure.
    have h_cl_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            closure (interior A) ×ˢ closure (interior B))
    simpa [h_cl_eq] using h_in_prod
  ------------------------------------------------------------------
  -- 2.  `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`.
  ------------------------------------------------------------------
  have hS_open : IsOpen (Set.prod (interior A) (interior B)) :=
    isOpen_interior.prod isOpen_interior
  have hS_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
    intro q hq
    exact And.intro
      ((interior_subset : interior A ⊆ A) hq.1)
      ((interior_subset : interior B ⊆ B) hq.2)
  have hS_sub_int :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) :=
    interior_maximal hS_sub hS_open
  ------------------------------------------------------------------
  -- 3.  Take closures and conclude.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B))
        ⊆ closure (interior (Set.prod A B)) :=
    closure_mono hS_sub_int
  exact h_closure_subset h_mem_closure_S

theorem P2_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  -- Split the point `p` into its coordinates.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P2` hypotheses on the two coordinates.
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hy_int : y ∈ interior (closure (interior B)) := hP2B hyB
  --------------------------------------------------------------------------------
  -- `S` is the product of the two open neighbourhoods obtained above.
  --------------------------------------------------------------------------------
  let S :=
    Set.prod (interior (closure (interior A))) (interior (closure (interior B)))
  have h_mem_S : (x, y) ∈ (S : Set (X × Y)) := by
    dsimp [S]; exact And.intro hx_int hy_int
  -- `S` is open.
  have hS_open : IsOpen (S : Set (X × Y)) := by
    dsimp [S]
    exact isOpen_interior.prod isOpen_interior
  --------------------------------------------------------------------------------
  -- 1.  Show that `S ⊆ closure (interior (A ×ˢ B))`.
  --------------------------------------------------------------------------------
  have hS_sub_closure :
      (S : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate lies in the appropriate closure.
    have hq1_cl :
        q.1 ∈ closure (interior A) :=
      (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A)) hq1
    have hq2_cl :
        q.2 ∈ closure (interior B) :=
      (interior_subset :
          interior (closure (interior B)) ⊆ closure (interior B)) hq2
    have h_in_prod_cl :
        (q : X × Y) ∈
          Set.prod (closure (interior A)) (closure (interior B)) :=
      And.intro hq1_cl hq2_cl
    -- Identify the previous product with a closure of a product.
    have h_closure_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using closure_prod_eq
    have hq_in_closure_prod :
        (q : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_closure_prod_eq] using h_in_prod_cl
    -- `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`.
    have hT_sub :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      -- Use `interior_maximal`.
      have hT_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        isOpen_interior.prod isOpen_interior
      have hT_subset :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro z hz
        exact And.intro
          ((interior_subset : interior A ⊆ A) hz.1)
          ((interior_subset : interior B ⊆ B) hz.2)
      exact interior_maximal hT_subset hT_open
    have h_closure_mono :
        closure (Set.prod (interior A) (interior B))
          ⊆ closure (interior (Set.prod A B)) :=
      closure_mono hT_sub
    exact h_closure_mono hq_in_closure_prod
  --------------------------------------------------------------------------------
  -- 2.  Since `S` is open and contained in the previous closure, it is contained
  --     in the interior of that closure.
  --------------------------------------------------------------------------------
  have hS_sub_inner :
      (S : Set (X × Y)) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal hS_sub_closure hS_open
  --------------------------------------------------------------------------------
  -- 3.  Conclude.
  --------------------------------------------------------------------------------
  exact hS_sub_inner h_mem_S

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A → P3 (f '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of `A`
  have hx_int : (x : X) ∈ interior (closure (A : Set X)) := hP3 hxA
  -- map this membership through `f`
  have h_mem_img : (f x : Y) ∈ f '' interior (closure (A : Set X)) :=
    ⟨x, hx_int, rfl⟩
  -- `f` sends interiors to interiors
  have h_img_int :
      f '' interior (closure (A : Set X)) =
        interior (f '' closure (A : Set X)) := by
    simpa using f.image_interior (s := closure (A : Set X))
  have h1 : (f x : Y) ∈ interior (f '' closure (A : Set X)) := by
    simpa [h_img_int] using h_mem_img
  -- `f` sends closures to closures
  have h_img_cl :
      f '' closure (A : Set X) = closure (f '' A) := by
    simpa using f.image_closure (s := A)
  -- rewrite and conclude
  have : (f x : Y) ∈ interior (closure (f '' A)) := by
    simpa [h_img_cl] using h1
  exact this