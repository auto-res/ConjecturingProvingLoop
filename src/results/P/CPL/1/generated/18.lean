

theorem P3_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior A) : P3 A := by
  intro x hx
  have hx_intA : x ∈ interior A := by
    have : x ∈ closure A := subset_closure hx
    simpa [h] using this
  simpa [h, interior_interior] using hx_intA

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Hence `e x` lies in `closure (e '' interior A)`
  have hx_closure_img : (e x) ∈ closure (e '' interior A : Set Y) := by
    -- First view it as an element of `e '' closure (interior A)`
    have h_mem : (e x) ∈ (e '' closure (interior A) : Set Y) :=
      ⟨x, hx_cl, rfl⟩
    -- Rewrite using `image_closure`
    simpa [e.image_closure (s := interior A)] using h_mem
  -- `e '' interior A` is exactly `interior (e '' A)`
  have h_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  -- Conclude the desired membership
  simpa [h_eq] using hx_closure_img

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  -- Start with a point `(x, y)` belonging to `A ×ˢ B`.
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P2` on each coordinate.
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  have hy : y ∈ interior (closure (interior B)) := hB hyB

  -- Define an auxiliary open rectangle around `(x, y)`.
  let U : Set (X × Y) :=
    Set.prod (interior (closure (interior A)))
             (interior (closure (interior B)))

  -- `U` is open.
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior : IsOpen (interior (closure (interior A)))).prod
      (isOpen_interior : IsOpen (interior (closure (interior B))))

  -- Show `U ⊆ closure (interior (A ×ˢ B))`.
  have hU_subset_closure :
      (U : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases q with ⟨u, v⟩
    dsimp [U] at hq
    rcases hq with ⟨hu, hv⟩
    -- Coordinates lie in the corresponding closures.
    have hu_cl : u ∈ closure (interior A) := interior_subset hu
    have hv_cl : v ∈ closure (interior B) := interior_subset hv
    -- A useful identification of closures of products.
    have h_cl_eq :
        (closure (Set.prod (interior A) (interior B)) :
            Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    -- Hence `(u, v)` is in the closure of the product of interiors.
    have h_mem_cl :
        ((u, v) : X × Y) ∈
          closure (Set.prod (interior A) (interior B)) := by
      have : ((u, v) : X × Y) ∈
          Set.prod (closure (interior A)) (closure (interior B)) :=
        ⟨hu_cl, hv_cl⟩
      simpa [h_cl_eq] using this
    -- The product of interiors is inside the interior of the product.
    have h_subset_prod_int :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- First inclusion into `A ×ˢ B`.
      have h_sub :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
            Set.prod A B :=
        Set.prod_mono interior_subset interior_subset
      -- Openness of the product of interiors.
      have h_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior : IsOpen (interior A)).prod
          (isOpen_interior : IsOpen (interior B))
      exact interior_maximal h_sub h_open
    -- Pass to closures.
    have h_closure_subset :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_subset_prod_int
    exact h_closure_subset h_mem_cl

  -- From the two previous facts,
  -- `U ⊆ interior (closure (interior (A ×ˢ B)))`.
  have hU_subset_int :
      (U : Set (X × Y)) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal hU_subset_closure hU_open

  -- `(x, y)` belongs to `U`, hence to the desired interior set.
  have hxyU : ((x, y) : X × Y) ∈ U := by
    dsimp [U]
    exact ⟨hx, hy⟩

  exact hU_subset_int hxyU

theorem P2_dense_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) = (⊤ : Set X) → P2 A := by
  intro h_dense
  -- From `P1 A` we know the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    closure_interior_eq_of_P1 (A := A) hA
  -- Hence `closure A` is also the whole space.
  have h_closureA_univ : closure A = (⊤ : Set X) := by
    simpa [h_eq] using h_dense
  -- Use the equivalence for dense sets to obtain `P2 A`.
  exact (P2_iff_P1_for_dense (A := A) h_closureA_univ).2 hA

theorem exists_P1_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ B, B ⊆ A ∧ P1 B := by
  exact ⟨A, ⟨subset_rfl, P1_of_P2 (A := A) hA⟩⟩

theorem P1_of_nhds {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, interior A ∈ 𝓝 x) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have h_mem : interior A ∈ 𝓝 x := h x hx
    exact mem_of_mem_nhds h_mem
  exact subset_closure hx_int