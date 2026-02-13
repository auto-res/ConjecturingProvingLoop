

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P3` on each coordinate.
  have hx : x ∈ interior (closure A) := hA hxA
  have hy : y ∈ interior (closure B) := hB hyB
  -- Define an auxiliary open rectangle around `(x, y)`.
  let U : Set (X × Y) :=
    Set.prod (interior (closure A)) (interior (closure B))
  -- `U` is open.
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior : IsOpen (interior (closure A))).prod
      (isOpen_interior : IsOpen (interior (closure B)))
  -- Show `U ⊆ closure (A ×ˢ B)`.
  have hU_subset_closure :
      (U : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases q with ⟨u, v⟩
    dsimp [U] at hq
    rcases hq with ⟨hu, hv⟩
    -- Coordinates lie in the corresponding closures.
    have hu_cl : u ∈ closure A := interior_subset hu
    have hv_cl : v ∈ closure B := interior_subset hv
    -- Identify the closure of the product.
    have h_cl_eq :
        (closure (Set.prod A B) : Set (X × Y)) =
          Set.prod (closure A) (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) =
            Set.prod (closure A) (closure B))
    -- Conclude membership.
    have h_mem : ((u, v) : X × Y) ∈ Set.prod (closure A) (closure B) :=
      ⟨hu_cl, hv_cl⟩
    simpa [h_cl_eq] using h_mem
  -- From the two previous facts,
  -- `U ⊆ interior (closure (A ×ˢ B))`.
  have hU_subset_int :
      (U : Set (X × Y)) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal hU_subset_closure hU_open
  -- `(x, y)` belongs to `U`, hence to the desired interior set.
  have hxyU : ((x, y) : X × Y) ∈ U := by
    dsimp [U]
    exact ⟨hx, hy⟩
  exact hU_subset_int hxyU

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (⊤ : Set X)) : P2 A := by
  intro x hx
  simpa [h, interior_univ]

theorem P3_closed_iff_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ interior A = closure A := by
  refine ⟨?forward, ?backward⟩
  · intro hP3
    -- From `P3` and closedness we get `interior A = A`.
    have h_int_eq_A : interior A = A :=
      interior_eq_of_P3_closed (A := A) hA hP3
    -- Replace `A` by `closure A` (which equals `A` because `A` is closed).
    have h_int_eq_cl : interior A = closure A := by
      calc
        interior A = A := h_int_eq_A
        _ = closure A := (hA.closure_eq).symm
    exact h_int_eq_cl
  · intro h_int_eq_cl
    -- Turn the given equality around to fit `P3_of_closure_eq_interior`.
    have h_cl_eq_int : closure A = interior A := h_int_eq_cl.symm
    exact P3_of_closure_eq_interior (A := A) h_cl_eq_int

theorem exists_closed_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, IsClosed B ∧ B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P2_empty⟩

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- `x` and `y` lie in the respective closures of the interiors.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- Hence `(x, y)` lies in the closure of the product of interiors.
  have h_mem_cl :
      ((x, y) : X × Y) ∈
        closure (Set.prod (interior A) (interior B)) := by
    -- Identify the closure explicitly.
    have h_eq :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    -- Membership follows from the coordinate facts.
    have : ((x, y) : X × Y) ∈
        Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hx_cl, hy_cl⟩
    simpa [h_eq] using this
  -- The closure of the product of interiors is contained in the desired closure.
  have h_subset :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
        closure (interior (Set.prod A B)) := by
    -- First, the product of interiors sits inside the interior of the product.
    have h_sub :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- `interior A ×ˢ interior B ⊆ A ×ˢ B`.
      have h₁ :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
            Set.prod A B :=
        Set.prod_mono interior_subset interior_subset
      -- The product of interiors is open.
      have h_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior : IsOpen (interior A)).prod
          (isOpen_interior : IsOpen (interior B))
      -- Apply `interior_maximal`.
      exact interior_maximal h₁ h_open
    -- Pass to closures.
    exact closure_mono h_sub
  exact h_subset h_mem_cl

theorem P3_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P1 A := by
  refine ⟨fun _ => P1_of_isOpen (A := A) hA,
         fun _ => P3_of_isOpen (A := A) hA⟩

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P2 A) : P2 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` belongs to the interior of `closure (interior A)`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Move the membership through the homeomorphism `e`
  have h1 : (e x) ∈ interior (e '' closure (interior A) : Set Y) := by
    -- first see it in the image of the interior
    have h_mem : (e x) ∈ (e '' interior (closure (interior A)) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    simpa [e.image_interior (s := closure (interior A))] using h_mem
  -- Rewrite the image of the closure via `e.image_closure`
  have h2 : (e x) ∈ interior (closure (e '' interior A : Set Y)) := by
    simpa [e.image_closure (s := interior A)] using h1
  -- Replace `e '' interior A` with `interior (e '' A)`
  have h_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  have h3 : (e x) ∈ interior (closure (interior (e '' A))) := by
    simpa [h_eq] using h2
  exact h3

theorem exists_P2_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P2 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P2_univ
  · simpa [closure_univ]